// This file is part of the Luau programming language and is licensed under MIT License; see LICENSE.txt for details
// This code is based on Lua 5.x implementation licensed under MIT License; see lua_LICENSE.txt for details
#include "lstring.h"

#include "lgc.h"
#include "lmem.h"

#include "Luau/StringHash.h"

#include <atomic>

#include <string.h>
#include <time.h>

#if defined(_WIN32)
// BCryptGenRandom, declared here rather than through <windows.h> and <bcrypt.h> and their macros. bcrypt.lib comes with
// every Windows SDK and MinGW. MSVC (and clang-cl, or clang in MSVC mode) links it from the pragma; MinGW, GCC or clang,
// ignores the pragma and needs -lbcrypt.
extern "C" __declspec(dllimport) long __stdcall BCryptGenRandom(void* algorithm, unsigned char* buffer, unsigned long size, unsigned long flags);
#if defined(_MSC_VER)
#pragma comment(lib, "bcrypt")
#endif
#elif defined(__APPLE__)
#include <sys/random.h>
#elif defined(__linux__)
#include <sys/syscall.h>
#include <unistd.h>
#endif

LUAU_FASTFLAGVARIABLE(LuauSaltedInterningTable)
LUAU_DYNAMIC_FASTINTVARIABLE(LuauStringHashSeed, 0)

#define salthash(hash, saltmult, saltadd) uint32_t((saltmult) * (hash) + (saltadd))
// the shift is 32 for a table of one bucket, so it's done in 64 bits
#define tobucket(hash, hashshift) int(uint64_t(hash) >> (hashshift))

unsigned int luaS_hash(const char* str, size_t len)
{
    // Note that this hashing algorithm is replicated in BytecodeBuilder.cpp, BytecodeBuilder::getStringHash
    unsigned int a = 0, b = 0;
    unsigned int h = unsigned(len);

    // hash prefix in 12b chunks (using aligned reads) with ARX based hash (LuaJIT v2.1, lookup3)
    // note that we stop at length<32 to maintain compatibility with Lua 5.1
    while (len >= 32)
    {
#define rol(x, s) ((x >> s) | (x << (32 - s)))
#define mix(u, v, w) a ^= h, a -= rol(h, u), b ^= a, b -= rol(a, v), h ^= b, h -= rol(b, w)

        // should compile into fast unaligned reads
        uint32_t block[3];
        memcpy(block, str, 12);

        a += block[0];
        b += block[1];
        h += block[2];
        mix(14, 11, 25);
        str += 12;
        len -= 12;

#undef mix
#undef rol
    }

    // original Lua 5.1 hash for compatibility (exact match when len<32)
    for (size_t i = len; i > 0; --i)
        h ^= (h << 5) + (h >> 2) + (uint8_t)str[i - 1];

    return h;
}

// The hash with DFFlag::LuauShortStringHash (Luau/StringHash.h, shared with the compiler's predicted slots)
unsigned int luaS_wordhash(const char* str, size_t len)
{
    return Luau::wordHash(str, len);
}

// Loads 8 bytes as a little-endian integer
static inline uint64_t loadle64(const char* p)
{
    uint64_t v;
    memcpy(&v, p, 8);
#if defined(__BYTE_ORDER__) && defined(__ORDER_BIG_ENDIAN__) && __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
    v = (uint64_t(Luau::loadLe32(p + 4)) << 32) | Luau::loadLe32(p);
#endif
    return v;
}

static inline uint64_t rotl64(uint64_t x, int s)
{
    return (x << s) | (x >> (64 - s));
}

static inline void sipround(uint64_t& v0, uint64_t& v1, uint64_t& v2, uint64_t& v3)
{
    v0 += v1;
    v1 = rotl64(v1, 13) ^ v0;
    v0 = rotl64(v0, 32);
    v2 += v3;
    v3 = rotl64(v3, 16) ^ v2;
    v0 += v3;
    v3 = rotl64(v3, 21) ^ v0;
    v2 += v1;
    v1 = rotl64(v1, 17) ^ v2;
    v2 = rotl64(v2, 32);
}

// SipHash-1-3 of len bytes (at least 8) under a 128-bit key
static uint64_t siphash13(const uint64_t key[2], const char* str, size_t len)
{
    LUAU_ASSERT(len >= 8);

    uint64_t v0 = key[0] ^ 0x736f6d6570736575ull;
    uint64_t v1 = key[1] ^ 0x646f72616e646f6dull;
    uint64_t v2 = key[0] ^ 0x6c7967656e657261ull;
    uint64_t v3 = key[1] ^ 0x7465646279746573ull;

    size_t tail = len & 7;
    for (const char* end = str + (len - tail); str != end; str += 8)
    {
        uint64_t m = loadle64(str);
        v3 ^= m;
        sipround(v0, v1, v2, v3);
        v0 ^= m;
    }

    // the last 0 to 7 bytes, taken from the top of the 8 bytes that end the string, and the length in the top byte
    uint64_t m = uint64_t(len) << 56;
    if (tail)
        m |= loadle64(str + tail - 8) >> (64 - 8 * tail);

    v3 ^= m;
    sipround(v0, v1, v2, v3);
    v0 ^= m;

    v2 ^= 0xff;
    sipround(v0, v1, v2, v3);
    sipround(v0, v1, v2, v3);
    sipround(v0, v1, v2, v3);

    return v0 ^ v1 ^ v2 ^ v3;
}

// The hash of a string of 32 bytes or more with DFFlag::LuauLongStringHash: SipHash-1-3 under the VM's random key, folded
// to 32 bits. Without the key, which the VM's code never exposes, nobody can compute it, so colliding strings can't be
// chosen in advance; and finding them from inside the VM (from table order or timing) gives as few bits as a random
// function. The hash of a shorter string stays unkeyed (Luau::wordHashShort): the compiler predicts its table slots and
// native code bakes it in, and the interning table's random salt keeps chosen short keys out of one bucket.
unsigned int luaS_longhash(const uint64_t key[2], const char* str, size_t len)
{
    uint64_t h = siphash13(key, str, len);
    return uint32_t(h ^ (h >> 32));
}

// Stores 8 bytes as a little-endian integer, so that a fixed seed gives the same key on every platform
static inline void storele64(char* p, uint64_t v)
{
    for (int i = 0; i < 8; i++)
        p[i] = char(v >> (8 * i));
}

// The VM's key and salt from entropy, or from DFInt::LuauStringHashSeed when it isn't 0
static void derivekeys(stringtable* tb, const char* data, size_t size)
{
    const uint64_t keys[3][2] = {{1, 0x9e3779b97f4a7c15ull}, {2, 0x9e3779b97f4a7c15ull}, {3, 0x9e3779b97f4a7c15ull}};
    tb->longkey[0] = siphash13(keys[0], data, size);
    tb->longkey[1] = siphash13(keys[1], data, size);

    uint64_t salt = siphash13(keys[2], data, size);
    tb->saltmult = uint32_t(salt) | 1;
    tb->saltadd = uint32_t(salt >> 32);
}

// Fills size bytes (at most 256) from the OS's random source, fresh for every VM, so that VMs made after a fork() differ
// from the parent's; false where there's none or the call fails. No library in between: no exceptions, no tokens.
static bool osrandom(char* data, size_t size)
{
    LUAU_ASSERT(size <= 256);
#if defined(_WIN32)
    const unsigned long systemPreferredRng = 2; // BCRYPT_USE_SYSTEM_PREFERRED_RNG
    return BCryptGenRandom(nullptr, reinterpret_cast<unsigned char*>(data), (unsigned long)size, systemPreferredRng) == 0;
#elif defined(__APPLE__)
    return getentropy(data, size) == 0; // macOS 10.12, iOS 10
#elif defined(__linux__) && defined(SYS_getrandom)
    // the syscall rather than getentropy, which glibc only has from 2.25; up to 256 bytes come whole once the kernel's
    // pool is ready, which it waits for (Linux 3.17)
    return syscall(SYS_getrandom, data, size, 0) == long(size);
#else
    (void)data;
    (void)size;
    return false;
#endif
}

// With DFFlag::LuauLongStringHash, gives the VM a random long-string key and a random interning-table salt
void luaS_initlonghash(global_State* g)
{
    stringtable* tb = &g->strt;
    tb->longhash = tb->wordhash && DFFlag::LuauLongStringHash;
    if (!tb->longhash)
        return;

    // before the table has a bucket: nothing is hashed yet
    LUAU_ASSERT(tb->size == 0);

    // A fixed seed gives every VM the same key and salt, and so the same iteration order (lua.h, lua_newstate), on every
    // platform: the seed is hashed as 8 little-endian bytes
    if (int seed = DFInt::LuauStringHashSeed)
    {
        char data[8];
        storele64(data, uint32_t(seed));
        derivekeys(tb, data, sizeof(data));
        return;
    }

    // The key and the salt from the OS (24 bytes), and always mixed with what differs between VMs and runs: the addresses
    // of the state, the stack and the code (each moved by ASLR), the clocks, and a count of VMs so that two made at once
    // differ. Where the OS gives nothing (no source above, or a failed call) those inputs are all there is, and the seed is
    // weak: a best effort, not a secret. A plugin sees heap addresses (tostring of a table) and the time.
    char data[3 * 8 + 7 * 8];
    size_t size = osrandom(data, 3 * 8) ? 3 * 8 : 0;

    static std::atomic<uint32_t> count{0};
    int local = 0;
    double now = lua_clock();
    uint64_t clockbits;
    memcpy(&clockbits, &now, sizeof(now));
    const uint64_t inputs[7] = {
        uint64_t(uintptr_t(g)),
        uint64_t(uintptr_t(&local)),
        uint64_t(uintptr_t(&luaS_initlonghash)),
        uint64_t(time(NULL)),
        uint64_t(clock()),
        clockbits,
        count.fetch_add(1, std::memory_order_relaxed),
    };
    for (uint64_t v : inputs)
    {
        storele64(data + size, v);
        size += 8;
    }
    LUAU_ASSERT(size <= sizeof(data));

    derivekeys(tb, data, size);
}

// With DFFlag::LuauLongStringHash, the salt for a host's pointer encoding key (lua_setpointerencodekey): the host's salt
// under the VM's own key, so that the table's buckets stay the VM's secret whatever the host passes
uint64_t luaS_keyedsalt(global_State* g, uint64_t hostsalt)
{
    LUAU_ASSERT(g->strt.longhash);
    char data[16];
    storele64(data, hostsalt);
    storele64(data + 8, 0x73616c74ull); // "salt", apart from the strings of 32 bytes or more the key hashes
    return siphash13(g->strt.longkey, data, sizeof(data));
}

// Equality of two strings of length len, with word compares for short strings
static inline bool streq(const char* a, const char* b, size_t len)
{
    if (len < 4)
        return len == 0 || (a[0] == b[0] && a[len >> 1] == b[len >> 1] && a[len - 1] == b[len - 1]);

    if (len <= 8)
    {
        uint32_t a0, a1, b0, b1;
        memcpy(&a0, a, 4);
        memcpy(&b0, b, 4);
        memcpy(&a1, a + len - 4, 4);
        memcpy(&b1, b + len - 4, 4);
        return ((a0 ^ b0) | (a1 ^ b1)) == 0;
    }

    if (len <= 32)
    {
        uint64_t diff = 0;
        for (size_t i = 0; i + 8 < len; i += 8)
        {
            uint64_t x, y;
            memcpy(&x, a + i, 8);
            memcpy(&y, b + i, 8);
            diff |= x ^ y;
        }

        uint64_t x, y;
        memcpy(&x, a + len - 8, 8);
        memcpy(&y, b + len - 8, 8);
        return (diff | (x ^ y)) == 0;
    }

    return memcmp(a, b, len) == 0;
}

// The VM's hash, chosen when the VM was created; strings already interned keep their hashes
static inline unsigned int strhash(const stringtable* tb, const char* str, size_t len)
{
    if (tb->wordhash)
    {
        if (len < 32)
            return Luau::wordHashShort(uint32_t(len), str, len);

        return tb->longhash ? luaS_longhash(tb->longkey, str, len) : Luau::wordHash(str, len);
    }

    return luaS_hash(str, len);
}

// Whether the interning table's buckets are salted: always with DFFlag::LuauLongStringHash, whose salt is random
static inline bool salted(const stringtable* tb)
{
    return FFlag::LuauSaltedInterningTable || tb->longhash;
}

static inline bool strmatch(const stringtable* tb, const TString* el, const char* str, size_t len)
{
    return el->len == len && (tb->wordhash ? streq(str, getstr(el), len) : memcmp(str, getstr(el), len) == 0);
}

static void luaS_rehash(lua_State* L, int newsize, uint32_t saltmult, uint32_t saltadd)
{
    global_State* g = L->global;
    TString** newhash = luaM_newarray(L, newsize, TString*, 0);
    stringtable* tb = &g->strt;
    uint8_t hashshift = uint8_t(32 - luaO_log2(unsigned(newsize)));
    for (int i = 0; i < newsize; i++)
        newhash[i] = NULL;
    // rehash
    for (int i = 0; i < tb->size; i++)
    {
        TString* p = tb->hash[i];
        while (p)
        {                            // for each node in the list
            TString* next = p->next; // save next
            unsigned int h = p->hash;
            unsigned int saltedh = salthash(h, saltmult, saltadd);
            int h1 = tobucket(saltedh, hashshift); // new position
            LUAU_ASSERT(unsigned(h1) < unsigned(newsize));
            p->next = newhash[h1]; // chain it
            newhash[h1] = p;
            p = next;
        }
    }
    luaM_freearray(L, tb->hash, tb->size, TString*, 0);
    tb->size = newsize;
    tb->hash = newhash;
    tb->saltmult = saltmult;
    tb->saltadd = saltadd;
    tb->hashshift = hashshift;
}

void luaS_resize(lua_State* L, int newsize)
{
    if (salted(&L->global->strt))
    {
        stringtable* tb = &L->global->strt;
        luaS_rehash(L, newsize, tb->saltmult, tb->saltadd);
    }
    else
    {
        TString** newhash = luaM_newarray(L, newsize, TString*, 0);
        stringtable* tb = &L->global->strt;
        for (int i = 0; i < newsize; i++)
            newhash[i] = NULL;
        // rehash
        for (int i = 0; i < tb->size; i++)
        {
            TString* p = tb->hash[i];
            while (p)
            {                            // for each node in the list
                TString* next = p->next; // save next
                unsigned int h = p->hash;
                int h1 = lmod(h, newsize); // new position
                LUAU_ASSERT(cast_int(h % newsize) == lmod(h, newsize));
                p->next = newhash[h1]; // chain it
                newhash[h1] = p;
                p = next;
            }
        }
        luaM_freearray(L, tb->hash, tb->size, TString*, 0);
        tb->size = newsize;
        tb->hash = newhash;
    }
}

void luaS_sethashsalt(lua_State* L, uint32_t saltmult, uint32_t saltadd)
{
    LUAU_ASSERT(salted(&L->global->strt));

    saltmult |= 1; // odd multiplier is required

    stringtable* tb = &L->global->strt;

    if (tb->saltmult == saltmult && tb->saltadd == saltadd)
        return;

    luaS_rehash(L, tb->size, saltmult, saltadd);
}

static TString* newlstr(lua_State* L, const char* str, size_t l, unsigned int h, unsigned int saltedh)
{
    if (l > MAXSSIZE)
        luaM_toobig(L);

    TString* ts = luaM_newgco(L, TString, sizestring(l), L->activememcat, LUA_TSTRING);
    luaC_init(L, ts, LUA_TSTRING);
    ts->atom = ATOM_UNDEF;
    ts->hash = h;
    ts->len = unsigned(l);

    memcpy(ts->data, str, l);
    ts->data[l] = '\0'; // ending 0

    stringtable* tb = &L->global->strt;

    if (salted(tb))
    {
        saltedh = tobucket(saltedh, tb->hashshift);
        ts->next = tb->hash[saltedh]; // chain new entry
        tb->hash[saltedh] = ts;
    }
    else
    {
        h = lmod(h, tb->size);
        ts->next = tb->hash[h]; // chain new entry
        tb->hash[h] = ts;
    }

    tb->nuse++;
    if (tb->nuse > cast_to(uint32_t, tb->size) && tb->size <= INT_MAX / 2)
        luaS_resize(L, tb->size * 2); // too crowded

    return ts;
}

TString* luaS_bufstart(lua_State* L, size_t size)
{
    if (size > MAXSSIZE)
        luaM_toobig(L);

    TString* ts = luaM_newgco(L, TString, sizestring(size), L->activememcat, LUA_TSTRING);
    luaC_init(L, ts, LUA_TSTRING);
    ts->atom = ATOM_UNDEF;
    ts->hash = 0; // computed in luaS_buffinish
    ts->len = unsigned(size);

    ts->next = NULL;

    return ts;
}

TString* luaS_buffinish(lua_State* L, TString* ts)
{
    stringtable* tb = &L->global->strt;
    unsigned int h = strhash(tb, ts->data, ts->len);
    unsigned int saltedh = salted(tb) ? salthash(h, tb->saltmult, tb->saltadd) : 0;
    int bucket = salted(tb) ? int(tobucket(saltedh, tb->hashshift)) : lmod(h, tb->size);

    // search if we already have this string in the hash table
    for (TString* el = tb->hash[bucket]; el != NULL; el = el->next)
    {
        if (strmatch(tb, el, ts->data, ts->len))
        {
            // string may be dead
            if (isdead(L->global, obj2gco(el)))
                changewhite(obj2gco(el));

            return el;
        }
    }

    LUAU_ASSERT(ts->next == NULL);

    ts->hash = h;
    ts->data[ts->len] = '\0'; // ending 0
    ts->atom = ATOM_UNDEF;
    ts->next = tb->hash[bucket]; // chain new entry
    tb->hash[bucket] = ts;

    tb->nuse++;
    if (tb->nuse > cast_to(uint32_t, tb->size) && tb->size <= INT_MAX / 2)
        luaS_resize(L, tb->size * 2); // too crowded

    return ts;
}

TString* luaS_newlstr(lua_State* L, const char* str, size_t l)
{
    if (salted(&L->global->strt))
    {
        global_State* g = L->global;
        unsigned int h = strhash(&g->strt, str, l);
        unsigned int saltedh = salthash(h, g->strt.saltmult, g->strt.saltadd);

        for (TString* el = g->strt.hash[tobucket(saltedh, g->strt.hashshift)]; el != NULL; el = el->next)
        {
            if (strmatch(&g->strt, el, str, l))
            {
                // string may be dead
                if (isdead(g, obj2gco(el)))
                    changewhite(obj2gco(el));
                return el;
            }
        }

        return newlstr(L, str, l, h, saltedh); // not found
    }
    else
    {
        unsigned int h = strhash(&L->global->strt, str, l);
        for (TString* el = L->global->strt.hash[lmod(h, L->global->strt.size)]; el != NULL; el = el->next)
        {
            if (strmatch(&L->global->strt, el, str, l))
            {
                // string may be dead
                if (isdead(L->global, obj2gco(el)))
                    changewhite(obj2gco(el));
                return el;
            }
        }
        return newlstr(L, str, l, h, 0); // not found
    }
}

static bool unlinkstr(lua_State* L, TString* ts)
{
    if (salted(&L->global->strt))
    {
        global_State* g = L->global;
        unsigned int saltedh = salthash(ts->hash, g->strt.saltmult, g->strt.saltadd);

        TString** p = &g->strt.hash[tobucket(saltedh, g->strt.hashshift)];

        while (TString* curr = *p)
        {
            if (curr == ts)
            {
                *p = curr->next;
                return true;
            }
            else
            {
                p = &curr->next;
            }
        }
    }
    else
    {
        global_State* g = L->global;

        TString** p = &g->strt.hash[lmod(ts->hash, g->strt.size)];

        while (TString* curr = *p)
        {
            if (curr == ts)
            {
                *p = curr->next;
                return true;
            }
            else
            {
                p = &curr->next;
            }
        }
    }

    return false;
}

void luaS_free(lua_State* L, TString* ts, lua_Page* page)
{
    if (unlinkstr(L, ts))
        L->global->strt.nuse--;
    else
        LUAU_ASSERT(ts->next == NULL); // orphaned string buffer

    luaM_freegco(L, ts, sizestring(ts->len), ts->memcat, page);
}
