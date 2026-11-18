// This file is part of the Luau programming language and is licensed under MIT License; see LICENSE.txt for details
// This code is based on Lua 5.x implementation licensed under MIT License; see lua_LICENSE.txt for details
#include "lualib.h"

#include "lapi.h"
#include "lnumutils.h"
#include "lstate.h"
#include "ltable.h"
#include "lstring.h"
#include "lgc.h"
#include "ldebug.h"
#include "lvm.h"

LUAU_DYNAMIC_FASTFLAGVARIABLE(LuauTableFindImprovement, false)
LUAU_DYNAMIC_FASTFLAGVARIABLE(LuauTableSortInterrupt, true)
LUAU_DYNAMIC_FASTFLAGVARIABLE(LuauTableFindInterrupt, true)
LUAU_DYNAMIC_FASTFLAGVARIABLE(LuauTableMoveBudget, true)
LUAU_DYNAMIC_FASTFLAGVARIABLE(LuauTableForeachInterrupt, true)

// calls the interrupt from a library function that runs no bytecode for a while; the interrupt can't yield there
LUAU_NOINLINE static void tablib_interrupt(lua_State* L)
{
    void (*interrupt)(lua_State*, int) = L->global->cb.interrupt;

    if (interrupt)
    {
        L->nCcalls++;
        interrupt(L, -1);
        L->nCcalls--;
    }
}

// a callback written in C runs no bytecode, and may itself call table.foreach with a C callback, and so on; with
// LuauTableForeachInterrupt, foreach and foreachi call the interrupt after each call of one
static void foreach_interrupt(lua_State* L)
{
    if (DFFlag::LuauTableForeachInterrupt && clvalue(&L->base[1])->isC)
        tablib_interrupt(L);
}

static int foreachi(lua_State* L)
{
    luaL_checktype(L, 1, LUA_TTABLE);
    luaL_checktype(L, 2, LUA_TFUNCTION);
    int i;
    int n = lua_objlen(L, 1);
    for (i = 1; i <= n; i++)
    {
        lua_pushvalue(L, 2);   // function
        lua_pushinteger(L, i); // 1st argument
        lua_rawgeti(L, 1, i);  // 2nd argument
        lua_call(L, 2, 1);
        foreach_interrupt(L);
        if (!lua_isnil(L, -1))
            return 1;
        lua_pop(L, 1); // remove nil result
    }
    return 0;
}

static int foreach (lua_State* L)
{
    luaL_checktype(L, 1, LUA_TTABLE);
    luaL_checktype(L, 2, LUA_TFUNCTION);
    lua_pushnil(L); // first key
    while (lua_next(L, 1))
    {
        lua_pushvalue(L, 2);  // function
        lua_pushvalue(L, -3); // key
        lua_pushvalue(L, -3); // value
        lua_call(L, 2, 1);
        foreach_interrupt(L);
        if (!lua_isnil(L, -1))
            return 1;
        lua_pop(L, 2); // remove value and result
    }
    return 0;
}

static int maxn(lua_State* L)
{
    double max = 0;
    luaL_checktype(L, 1, LUA_TTABLE);

    LuaTable* t = hvalue(L->base);

    for (int i = 0; i < t->sizearray; i++)
    {
        if (!ttisnil(&t->array[i]))
            max = i + 1;
    }

    for (int i = 0; i < sizenode(t); i++)
    {
        LuaNode* n = gnode(t, i);

        if (!ttisnil(gval(n)) && ttisnumber(gkey(n)))
        {
            double v = nvalue(gkey(n));

            if (v > max)
                max = v;
        }
    }

    lua_pushnumber(L, max);
    return 1;
}

static int getn(lua_State* L)
{
    luaL_checktype(L, 1, LUA_TTABLE);
    lua_pushinteger(L, lua_objlen(L, 1));
    return 1;
}

static bool shouldsparsemove(LuaTable* src, LuaTable* dst, int n)
{
    int srcelems = src->sizearray + sizenode(src);
    int dstelems = dst->sizearray + sizenode(dst);
    int maxelems = srcelems > dstelems ? srcelems : dstelems;
    const int minsparsemoveelems = 32;

    return n > minsparsemoveelems && n / 2 > maxelems;
}

static bool tovalidintkey(lua_State* L, int idx, int f, int e, int* result)
{
    if (lua_type(L, idx) == LUA_TNUMBER)
    {
        double nkey = lua_tonumber(L, idx);

        if (nkey >= f && nkey <= e)
        {
            luai_num2int(*result, nkey);
            return luai_numeq(cast_num(*result), nkey);
        }
    }

    return false;
}

// with LuauTableMoveBudget, a move that goes element by element calls the interrupt after each this many elements
const int kMoveInterruptElements = 1024;

// moveelements' element by element move of n elements, with LuauTableMoveBudget; backward moves the last one first
LUAU_NOINLINE static void movebudget(lua_State* L, int srct, int dstt, LuaTable* dst, int f, int t, int n, bool backward)
{
    int step = backward ? -1 : 1;
    int budget = kMoveInterruptElements;

    for (int k = 0, i = backward ? n - 1 : 0; k < n; ++k, i += step)
    {
        if (LUAU_UNLIKELY(budget-- == 0))
        {
            budget = kMoveInterruptElements - 1;
            tablib_interrupt(L);

            // the interrupt may freeze the destination, and the move must not write to it after that
            if (dst->readonly)
                luaG_readonlyerror(L);
        }

        lua_rawgeti(L, srct, f + i);

        // writing nil to an absent key would add a node for it, and a table whose free nodes run out rehashes on each
        // such write without growing, since nil values don't count towards its size
        if (ttisnil(L->top - 1) && ttisnil(luaH_getnum(dst, t + i)))
            L->top--;
        else
            lua_rawseti(L, dstt, t + i);
    }
}

static void moveelements(lua_State* L, int srct, int dstt, int f, int e, int t, bool sparsemove)
{
    LuaTable* src = hvalue(L->base + (srct - 1));
    LuaTable* dst = hvalue(L->base + (dstt - 1));

    if (dst->readonly)
        luaG_readonlyerror(L);

    int n = e - f + 1; // number of elements to move

    if (unsigned(f) - 1 < unsigned(src->sizearray) && unsigned(t) - 1 < unsigned(dst->sizearray) &&
        unsigned(f) - 1 + unsigned(n) <= unsigned(src->sizearray) && unsigned(t) - 1 + unsigned(n) <= unsigned(dst->sizearray))
    {
        TValue* srcarray = src->array;
        TValue* dstarray = dst->array;

        if (t > e || t <= f || (dstt != srct && dst != src))
        {
            for (int i = 0; i < n; ++i)
            {
                TValue* s = &srcarray[f + i - 1];
                TValue* d = &dstarray[t + i - 1];
                setobj2t(L, d, s);
            }
        }
        else
        {
            for (int i = n - 1; i >= 0; i--)
            {
                TValue* s = &srcarray[(f + i) - 1];
                TValue* d = &dstarray[(t + i) - 1];
                setobj2t(L, d, s);
            }
        }

        luaC_barrierfast(L, dst);
    }
    else if (sparsemove)
    {
        int srcta = lua_absindex(L, srct);
        int dstta = lua_absindex(L, dstt);

        int te = t + (n - 1);

        // temporary table to hold elements from source that are being moved
        lua_newtable(L);

        // collect integer key elements that are being moved
        for (int iter = 0; (iter = lua_rawiter(L, srcta, iter)) != -1;)
        {
            int ikey = 0;
            if (tovalidintkey(L, -2, f, e, &ikey))
                lua_rawseti(L, -3, ikey); // pops value
            else
                lua_pop(L, 1); // pop value

            lua_pop(L, 1); // pop key
        }

        // clear the destination range
        for (int iter = 0; (iter = lua_rawiter(L, dstta, iter)) != -1;)
        {
            int ikey = 0;
            if (tovalidintkey(L, -2, t, te, &ikey))
            {
                lua_pushnil(L);
                lua_rawseti(L, dstta, ikey);
            }

            lua_pop(L, 2);
        }

        // copy the elements from the temporary table to the destination table
        for (int iter = 0; (iter = lua_rawiter(L, -1, iter)) != -1;)
        {
            int ikey = lua_tointeger(L, -2);
            lua_rawseti(L, dstta, ikey - f + t);
            lua_pop(L, 1);
        }

        lua_pop(L, 1);
    }
    else if (DFFlag::LuauTableMoveBudget)
    {
        movebudget(L, srct, dstt, dst, f, t, n, /* backward */ !(t > e || t <= f || dst != src));
    }
    else
    {
        if (t > e || t <= f || dst != src)
        {
            for (int i = 0; i < n; ++i)
            {
                lua_rawgeti(L, srct, f + i);
                lua_rawseti(L, dstt, t + i);
            }
        }
        else
        {
            for (int i = n - 1; i >= 0; i--)
            {
                lua_rawgeti(L, srct, f + i);
                lua_rawseti(L, dstt, t + i);
            }
        }
    }
}

static int tinsert(lua_State* L)
{
    luaL_checktype(L, 1, LUA_TTABLE);
    int n = lua_objlen(L, 1);
    int pos; // where to insert new element
    switch (lua_gettop(L))
    {
    case 2:
    {                // called with only 2 arguments
        pos = n + 1; // insert new element at the end
        break;
    }
    case 3:
    {
        pos = luaL_checkinteger(L, 2); // 2nd argument is the position

        // move up elements if necessary
        if (1 <= pos && pos <= n)
            moveelements(L, 1, 1, pos, n, pos + 1, /* sparsemove */ false);
        break;
    }
    default:
    {
        luaL_error(L, "wrong number of arguments to 'insert'");
    }
    }
    lua_rawseti(L, 1, pos); // t[pos] = v
    return 0;
}

static int tremove(lua_State* L)
{
    luaL_checktype(L, 1, LUA_TTABLE);
    int n = lua_objlen(L, 1);
    int pos = luaL_optinteger(L, 2, n);

    if (!(1 <= pos && pos <= n)) // position is outside bounds?
        return 0;                // nothing to remove
    lua_rawgeti(L, 1, pos);      // result = t[pos]

    moveelements(L, 1, 1, pos + 1, n, pos, /* sparsemove */ false);

    lua_pushnil(L);
    lua_rawseti(L, 1, n); // t[n] = nil
    return 1;
}

/*
** Copy elements (1[f], ..., 1[e]) into (tt[t], tt[t+1], ...). Whenever
** possible, copy in increasing order, which is better for rehashing.
** "possible" means destination after original range, or smaller
** than origin, or copying to another table.
*/
static int tmove(lua_State* L)
{
    luaL_checktype(L, 1, LUA_TTABLE);
    int f = luaL_checkinteger(L, 2);
    int e = luaL_checkinteger(L, 3);
    int t = luaL_checkinteger(L, 4);
    int tt = !lua_isnoneornil(L, 5) ? 5 : 1; // destination table
    luaL_checktype(L, tt, LUA_TTABLE);

    if (e >= f)
    { // otherwise, nothing to move
        luaL_argcheck(L, f > 0 || e < INT_MAX + f, 3, "too many elements to move");
        int n = e - f + 1; // number of elements to move
        luaL_argcheck(L, t <= INT_MAX - n + 1, 4, "destination wrap around");

        LuaTable* dst = hvalue(L->base + (tt - 1));

        if (dst->readonly) // also checked in moveelements, but this blocks resizes of r/o tables
            luaG_readonlyerror(L);

        bool sparsemove = shouldsparsemove(hvalue(L->base), dst, n);

        if (t > 0 && (t - 1) <= dst->sizearray && (t - 1 + n) > dst->sizearray)
        { // grow the destination table array
            luaH_resizearray(L, dst, t - 1 + n);
        }

        moveelements(L, 1, tt, f, e, t, sparsemove);
    }
    lua_pushvalue(L, tt); // return destination table
    return 1;
}

static void addfield(lua_State* L, luaL_Strbuf* b, int i, LuaTable* t)
{
    if (t && unsigned(i) - 1 < unsigned(t->sizearray) && ttisstring(&t->array[i - 1]))
    {
        TString* ts = tsvalue(&t->array[i - 1]);
        luaL_addlstring(b, getstr(ts), ts->len);
    }
    else
    {
        int tt = lua_rawgeti(L, 1, i);
        if (tt != LUA_TSTRING && tt != LUA_TNUMBER)
            luaL_error(L, "invalid value (%s) at index %d in table for 'concat'", luaL_typename(L, -1), i);
        luaL_addvalue(b);
    }
}

static int tconcat(lua_State* L)
{
    size_t lsep;
    const char* sep = luaL_optlstring(L, 2, "", &lsep);
    luaL_checktype(L, 1, LUA_TTABLE);
    int i = luaL_optinteger(L, 3, 1);
    int last = luaL_opt(L, luaL_checkinteger, 4, lua_objlen(L, 1));

    LuaTable* t = hvalue(L->base);

    luaL_Strbuf b;
    luaL_buffinit(L, &b);
    for (; i < last; i++)
    {
        addfield(L, &b, i, t);
        if (lsep != 0)
            luaL_addlstring(&b, sep, lsep);
    }
    if (i == last) // add last value (if interval was not empty)
        addfield(L, &b, i, t);
    luaL_pushresult(&b);
    return 1;
}

static int tpack(lua_State* L)
{
    int n = lua_gettop(L);    // number of elements to pack
    lua_createtable(L, n, 1); // create result table

    LuaTable* t = hvalue(L->top - 1);

    for (int i = 0; i < n; ++i)
    {
        TValue* e = &t->array[i];
        setobj2t(L, e, L->base + i);
    }

    // t.n = number of elements
    TValue* nv = luaH_setstr(L, t, luaS_newliteral(L, "n"));
    setnvalue(nv, n);

    return 1; // return table
}

static int tunpack(lua_State* L)
{
    luaL_checktype(L, 1, LUA_TTABLE);
    LuaTable* t = hvalue(L->base);

    int i = luaL_optinteger(L, 2, 1);
    int e = luaL_opt(L, luaL_checkinteger, 3, lua_objlen(L, 1));
    if (i > e)
        return 0;                 // empty range
    unsigned n = (unsigned)e - i; // number of elements minus 1 (avoid overflows)
    if (n >= (unsigned int)INT_MAX || !lua_checkstack(L, (int)(++n)))
        luaL_error(L, "too many results to unpack");

    // fast-path: direct array-to-stack copy
    if (i == 1 && int(n) <= t->sizearray)
    {
        for (i = 0; i < int(n); i++)
            setobj2s(L, L->top + i, &t->array[i]);
        L->top += n;
    }
    else
    {
        // push arg[i..e - 1] (to avoid overflows)
        for (; i < e; i++)
            lua_rawgeti(L, 1, i);
        lua_rawgeti(L, 1, e); // push last element
    }
    return (int)n;
}

typedef int (*SortPredicate)(lua_State* L, const TValue* l, const TValue* r);

// with LuauTableSortInterrupt, a sort calls the interrupt for bounded work, since it may run no bytecode for a long time:
// once for each kSortInterruptElements elements it partitions (counting only ranges of kSortInterruptRange or more), each
// time heap sort has placed kSortInterruptPlacements elements, for each kSortInterruptBytes bytes of strings it compares,
// and after each call of a comparator or metamethod written in C
const int kSortInterruptElements = 1024;
const int kSortInterruptRange = 256;
const int kSortInterruptPlacements = 16;
const int kSortInterruptBytes = 65536;

// strings that share a first byte and are both this long or longer are compared in slices and charged by the bytes
// compared; shorter ones cost little more than a comparison of numbers
const size_t kSortStringCharged = 256;

// a callback may freeze the table being sorted, and the sort must not write to it after that
static void sort_checkreadonly(lua_State* L)
{
    if (hvalue(L->base)->readonly)
        luaG_readonlyerror(L);
}

static int sort_func(lua_State* L, const TValue* l, const TValue* r)
{
    LUAU_ASSERT(L->top == L->base + 2); // table, function

    setobj2s(L, L->top, &L->base[1]);
    setobj2s(L, L->top + 1, l);
    setobj2s(L, L->top + 2, r);
    L->top += 3; // safe because of LUA_MINSTACK guarantee
    luaD_call(L, L->top - 3, 1);
    L->top -= 1; // maintain stack depth

    int res = !l_isfalse(L->top);

    if (DFFlag::LuauTableSortInterrupt)
    {
        // a comparator written in Luau reaches the interrupt through its own safepoints
        if (clvalue(&L->base[1])->isC)
            tablib_interrupt(L);

        sort_checkreadonly(L);
    }

    return res;
}

// without a comparator, the sort's slot for it holds the bytes of strings compared since the last interrupt; the strings
// being compared stay alive while the interrupt runs, since it may change the table
static void sort_chargebytes(lua_State* L, TString* ls, TString* rs, size_t bytes)
{
    double total = nvalue(&L->base[1]) + double(bytes);

    if (total >= kSortInterruptBytes)
    {
        total -= kSortInterruptBytes;

        setsvalue(L, L->top, ls);
        setsvalue(L, L->top + 1, rs);
        L->top += 2; // safe because of LUA_MINSTACK guarantee
        tablib_interrupt(L);
        L->top -= 2;

        sort_checkreadonly(L);
    }

    setnvalue(&L->base[1], total); // the interrupt may reallocate the stack
}

// luaV_strcmp for strings that share a first byte and are both long: compares slices that grow up to half the
// interrupt's share of bytes, and charges each one
LUAU_NOINLINE static int sort_strcmp(lua_State* L, TString* ls, TString* rs)
{
    size_t ll = ls->len;
    size_t lr = rs->len;
    size_t lmin = ll < lr ? ll : lr;

    int res = 0;
    size_t slice = kSortStringCharged;

    for (size_t pos = 0; pos < lmin && res == 0; pos += slice, slice = slice < kSortInterruptBytes / 2 ? slice * 2 : slice)
    {
        size_t len = lmin - pos < slice ? lmin - pos : slice;
        res = memcmp(getstr(ls) + pos, getstr(rs) + pos, len);
        sort_chargebytes(L, ls, rs, len);
    }

    if (res != 0)
        return res;

    return ll == lr ? 0 : ll < lr ? -1 : 1;
}

// luaV_strcmp(ls, rs) < 0, apart from strings that share a first byte and are both long
LUAU_NOINLINE static int sort_strlessthan(lua_State* L, TString* ls, TString* rs)
{
    if (ls == rs)
        return 0;

    const char* lp = getstr(ls);
    const char* rp = getstr(rs);

    // always safe to read one character because even empty strings are nul terminated
    if (*lp != *rp)
        return uint8_t(*lp) < uint8_t(*rp);

    size_t lmin = ls->len < rs->len ? ls->len : rs->len;

    if (LUAU_UNLIKELY(lmin >= kSortStringCharged))
        return sort_strcmp(L, ls, rs) < 0;

    int res = memcmp(lp, rp, lmin);
    return res != 0 ? res < 0 : ls->len < rs->len;
}

// other types either raise an error or call a metamethod, which may be written in C and run no bytecode
LUAU_NOINLINE static int sort_metalessthan(lua_State* L, const TValue* l, const TValue* r)
{
    int res = luaV_lessthan(L, l, r);

    tablib_interrupt(L);
    sort_checkreadonly(L);

    return res;
}

// luaV_lessthan with bounded work between interrupts
static int sort_lessthan(lua_State* L, const TValue* l, const TValue* r)
{
    if (LUAU_LIKELY(ttisnumber(l) && ttisnumber(r)))
        return luai_numlt(nvalue(l), nvalue(r));

    if (ttisstring(l) && ttisstring(r))
        return sort_strlessthan(L, tsvalue(l), tsvalue(r));

    return sort_metalessthan(L, l, r);
}

inline void sort_swap(lua_State* L, LuaTable* t, int i, int j)
{
    TValue* arr = t->array;
    int n = t->sizearray;
    LUAU_ASSERT(unsigned(i) < unsigned(n) && unsigned(j) < unsigned(n)); // contract maintained in sort_less after predicate call

    // no barrier required because both elements are in the array before and after the swap
    TValue temp;
    setobj2s(L, &temp, &arr[i]);
    setobj2t(L, &arr[i], &arr[j]);
    setobj2t(L, &arr[j], &temp);
}

inline int sort_less(lua_State* L, LuaTable* t, int i, int j, SortPredicate pred)
{
    TValue* arr = t->array;
    int n = t->sizearray;
    LUAU_ASSERT(unsigned(i) < unsigned(n) && unsigned(j) < unsigned(n)); // contract maintained in sort_less after predicate call

    int res = pred(L, &arr[i], &arr[j]);

    // predicate call may resize the table, which is invalid
    if (t->sizearray != n)
        luaL_error(L, "table modified during sorting");

    return res;
}

// calls the interrupt for work the sort did without one, when there's no comparator
LUAU_NOINLINE static void sort_interrupt(lua_State* L, LuaTable* t, SortPredicate pred, int calls)
{
    if (pred != sort_lessthan)
        return;

    int n = t->sizearray;

    for (int i = 0; i < calls; ++i)
        tablib_interrupt(L);

    // interrupt call may resize the table, which is invalid
    if (t->sizearray != n)
        luaL_error(L, "table modified during sorting");

    sort_checkreadonly(L);
}

static void sort_siftheap(lua_State* L, LuaTable* t, int l, int u, SortPredicate pred, int root)
{
    LUAU_ASSERT(l <= u);
    int count = u - l + 1;

    // process all elements with two children
    while (root * 2 + 2 < count)
    {
        int left = root * 2 + 1, right = root * 2 + 2;
        int next = root;
        next = sort_less(L, t, l + next, l + left, pred) ? left : next;
        next = sort_less(L, t, l + next, l + right, pred) ? right : next;

        if (next == root)
            break;

        sort_swap(L, t, l + root, l + next);
        root = next;
    }

    // process last element if it has just one child
    int lastleft = root * 2 + 1;
    if (lastleft == count - 1 && sort_less(L, t, l + root, l + lastleft, pred))
        sort_swap(L, t, l + root, l + lastleft);
}

static void sort_heap(lua_State* L, LuaTable* t, int l, int u, SortPredicate pred)
{
    LUAU_ASSERT(l <= u);
    int count = u - l + 1;

    for (int i = count / 2 - 1; i >= 0; --i)
    {
        if (i % kSortInterruptPlacements == 0)
            sort_interrupt(L, t, pred, 1);

        sort_siftheap(L, t, l, u, pred, i);
    }

    for (int i = count - 1; i > 0; --i)
    {
        if (i % kSortInterruptPlacements == 0)
            sort_interrupt(L, t, pred, 1);

        sort_swap(L, t, l, l + i);
        sort_siftheap(L, t, l, l + i - 1, pred, 0);
    }
}

static void sort_rec(lua_State* L, LuaTable* t, int l, int u, int limit, SortPredicate pred)
{
    // sort range [l..u] (inclusive, 0-based)
    while (l < u)
    {
        // if the limit has been reached, quick sort is going over the permitted nlogn complexity, so we fall back to heap sort
        if (limit == 0)
            return sort_heap(L, t, l, u, pred);

        // sort elements a[l], a[(l+u)/2] and a[u]
        // note: this simultaneously acts as a small sort and a median selector
        if (sort_less(L, t, u, l, pred)) // a[u] < a[l]?
            sort_swap(L, t, u, l);       // swap a[l] - a[u]
        if (u - l == 1)
            break;                       // only 2 elements
        int m = l + ((u - l) >> 1);      // midpoint
        if (sort_less(L, t, m, l, pred)) // a[m]<a[l]?
            sort_swap(L, t, m, l);
        else if (sort_less(L, t, u, m, pred)) // a[u]<a[m]?
            sort_swap(L, t, m, u);
        if (u - l == 2)
            break; // only 3 elements

        // here l, m, u are ordered; m will become the new pivot
        int p = u - 1;
        sort_swap(L, t, m, u - 1); // pivot is now (and always) at u-1

        // a[l] <= P == a[u-1] <= a[u], only need to sort from l+1 to u-2
        int i = l;
        int j = u - 1;
        for (;;)
        { // invariant: a[l..i] <= P <= a[j..u]
            // repeat ++i until a[i] >= P
            while (sort_less(L, t, ++i, p, pred))
            {
                if (i >= u)
                    luaL_error(L, "invalid order function for sorting");
            }
            // repeat --j until a[j] <= P
            while (sort_less(L, t, p, --j, pred))
            {
                if (j <= l)
                    luaL_error(L, "invalid order function for sorting");
            }
            if (j < i)
                break;
            sort_swap(L, t, i, j);
        }

        // swap pivot a[p] with a[i], which is the new midpoint
        sort_swap(L, t, p, i);

        // the work between two interrupts is at most one partition and the sorting of two ranges smaller than
        // kSortInterruptRange, apart from the work string comparisons and metamethods charge themselves
        if (u - l + 1 >= kSortInterruptRange)
            sort_interrupt(L, t, pred, (u - l + kSortInterruptElements) / kSortInterruptElements);

        // adjust limit to allow 1.5 log2N recursive steps
        limit = (limit >> 1) + (limit >> 2);

        // a[l..i-1] <= a[i] == P <= a[i+1..u]
        // sort smaller half recursively; the larger half is sorted in the next loop iteration
        if (i - l < u - i)
        {
            sort_rec(L, t, l, i - 1, limit, pred);
            l = i + 1;
        }
        else
        {
            sort_rec(L, t, i + 1, u, limit, pred);
            u = i - 1;
        }
    }
}

static int tsort(lua_State* L)
{
    luaL_checktype(L, 1, LUA_TTABLE);
    LuaTable* t = hvalue(L->base);
    int n = luaH_getn(t);
    if (t->readonly)
        luaG_readonlyerror(L);

    SortPredicate pred = DFFlag::LuauTableSortInterrupt ? sort_lessthan : luaV_lessthan;
    if (!lua_isnoneornil(L, 2)) // is there a 2nd argument?
    {
        luaL_checktype(L, 2, LUA_TFUNCTION);
        pred = sort_func;
    }
    lua_settop(L, 2); // make sure there are two arguments

    if (pred == sort_lessthan)
        setnvalue(&L->base[1], 0); // bytes of strings compared since the last interrupt; see sort_chargebytes

    if (n > 0)
        sort_rec(L, t, 0, n - 1, n, pred);
    return 0;
}

static int tcreate(lua_State* L)
{
    int size = luaL_checkinteger(L, 1);
    if (size < 0)
        luaL_argerror(L, 1, "size out of range");

    if (!lua_isnoneornil(L, 2))
    {
        lua_createtable(L, size, 0);
        LuaTable* t = hvalue(L->top - 1);

        StkId v = L->base + 1;

        for (int i = 0; i < size; ++i)
        {
            TValue* e = &t->array[i];
            setobj2t(L, e, v);
        }
    }
    else
    {
        lua_createtable(L, size, 0);
    }

    return 1;
}

// tfind's search with LuauTableFindInterrupt for a value with an __eq metamethod, which may be written in C and run no
// bytecode, or from an index close enough to INT_MAX for the next one to overflow: calls the interrupt after each
// comparison that may call __eq, and stops after INT_MAX
LUAU_NOINLINE static int findguarded(lua_State* L, LuaTable* t, int init)
{
    for (int i = init;; ++i)
    {
        const TValue* e = luaH_getnum(t, i);
        if (ttisnil(e))
            break;

        StkId v = L->base + 1;
        bool call = ttype(e) == ttype(v);
        bool found = equalobj(L, v, e);

        if (call)
            tablib_interrupt(L);

        if (found)
        {
            lua_pushinteger(L, i);
            return 1;
        }

        if (i == INT_MAX)
            break;
    }

    lua_pushnil(L);
    return 1;
}

static int tfind(lua_State* L)
{
    int init = 1;

    if (DFFlag::LuauTableFindImprovement)
    {
        int nargs = int(L->top - L->base);

        if (nargs < 1 || !ttistable(L->base))
            luaL_checktype(L, 1, LUA_TTABLE);
        if (nargs < 2)
            luaL_checkany(L, 2);
        if (nargs >= 3 && !ttisnil(L->base + 2))
            init = luaL_checkinteger(L, 3);
    }
    else
    {
        luaL_checktype(L, 1, LUA_TTABLE);
        luaL_checkany(L, 2);
        init = luaL_optinteger(L, 3, 1);
    }

    if (init < 1)
        luaL_argerror(L, 3, "index out of range");

    LuaTable* t = hvalue(L->base);

    if (DFFlag::LuauTableFindImprovement)
    {
        if (init > t->sizearray && t->node == &luaH_dummynode)
        {
            lua_pushnil(L);
            return 1;
        }

        // Fast array search can only be performed when metamethod is absent/not used, as it can mutate table and relocate stack
        if (!iscollectable(L->base + 1) || ttisnil(luaT_gettmbyobj(L, L->base + 1, TM_EQ)))
        {
            if (int index = luaH_rawfind(t, init, L->base + 1))
                lua_pushinteger(L, index);
            else
                lua_pushnil(L);

            return 1;
        }
    }

    // only the value's __eq can be called, and nothing else runs if it has none; then the table doesn't change, and the
    // search goes through at most as many indices as the table has room for, so the next one can't overflow unless init
    // is that close to INT_MAX
    if (DFFlag::LuauTableFindInterrupt && ((iscollectable(L->base + 1) && !ttisnil(luaT_gettmbyobj(L, L->base + 1, TM_EQ))) ||
                                              init > INT_MAX - t->sizearray - sizenode(t)))
        return findguarded(L, t, init);

    for (int i = init;; ++i)
    {
        const TValue* e = luaH_getnum(t, i);
        if (ttisnil(e))
            break;

        StkId v = L->base + 1;

        if (equalobj(L, v, e))
        {
            lua_pushinteger(L, i);
            return 1;
        }
    }

    lua_pushnil(L);
    return 1;
}

static int tclear(lua_State* L)
{
    luaL_checktype(L, 1, LUA_TTABLE);

    LuaTable* tt = hvalue(L->base);
    if (tt->readonly)
        luaG_readonlyerror(L);

    luaH_clear(tt);
    return 0;
}

static int tfreeze(lua_State* L)
{
    luaL_checktype(L, 1, LUA_TTABLE);
    luaL_argcheck(L, !lua_getreadonly(L, 1), 1, "table is already frozen");
    luaL_argcheck(L, !luaL_getmetafield(L, 1, "__metatable"), 1, "table has a protected metatable");

    lua_setreadonly(L, 1, true);

    lua_pushvalue(L, 1);
    return 1;
}

static int tisfrozen(lua_State* L)
{
    luaL_checktype(L, 1, LUA_TTABLE);

    lua_pushboolean(L, lua_getreadonly(L, 1));
    return 1;
}

static int tclone(lua_State* L)
{
    luaL_checktype(L, 1, LUA_TTABLE);
    luaL_argcheck(L, !luaL_getmetafield(L, 1, "__metatable"), 1, "table has a protected metatable");

    LuaTable* tt = luaH_clone(L, hvalue(L->base));

    TValue v;
    sethvalue(L, &v, tt);
    luaA_pushvalue(L, &v);

    return 1;
}

static const luaL_Reg tab_funcs[] = {
    {"concat", tconcat},
    {"foreach", foreach},
    {"foreachi", foreachi},
    {"getn", getn},
    {"maxn", maxn},
    {"insert", tinsert},
    {"remove", tremove},
    {"sort", tsort},
    {"pack", tpack},
    {"unpack", tunpack},
    {"move", tmove},
    {"create", tcreate},
    {"find", tfind},
    {"clear", tclear},
    {"freeze", tfreeze},
    {"isfrozen", tisfrozen},
    {"clone", tclone},
    {NULL, NULL},
};

int luaopen_table(lua_State* L)
{
    luaL_register(L, LUA_TABLIBNAME, tab_funcs);

    // Lua 5.1 compat
    lua_pushcfunction(L, tunpack, "unpack");
    lua_setglobal(L, "unpack");

    return 1;
}
