// This file is part of the Luau programming language and is licensed under MIT License; see LICENSE.txt for details
#pragma once

#include "Luau/Common.h"

#include <stddef.h>
#include <stdint.h>
#include <string.h>

// The string hash of DFFlag::LuauShortStringHash, shared by the VM (luaS_wordhash) and the compiler
// (BytecodeBuilder::getStringHash), so that the compiler's predicted slots match the VM's table slots.
//
// The VM reads the flag once, when a state is created (lua_newstate), and keeps that hash for the state's life. The
// compiler reads it each time it computes a hash. A chunk compiled with the flag in one state and loaded into a VM
// created with the other state (another process, or the flag changed in between) still runs correctly: its
// predicted slots miss on first use, and the VM patches each instruction on its first miss.
LUAU_DYNAMIC_FASTFLAG(LuauShortStringHash)

// With DFFlag::LuauLongStringHash (and DFFlag::LuauShortStringHash), each VM hashes a string of 32 bytes or more with
// its own key (luaS_longhash), which the compiler can't know: its predicted slots for such strings miss once.
LUAU_DYNAMIC_FASTFLAG(LuauLongStringHash)

namespace Luau
{

// Loads 4 bytes as a little-endian integer, so that the hash is the same on every platform
inline uint32_t loadLe32(const char* p)
{
    uint32_t v;
    memcpy(&v, p, 4);
#if defined(__BYTE_ORDER__) && defined(__ORDER_BIG_ENDIAN__) && __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
    v = (v >> 24) | ((v >> 8) & 0xff00) | ((v << 8) & 0xff0000) | (v << 24);
#endif
    return v;
}

// Whether a VM created with the current flags hashes a string of this length with its own key, so that no hash the
// compiler computes predicts its slot
inline bool isStringHashKeyed(size_t len)
{
    return DFFlag::LuauShortStringHash && DFFlag::LuauLongStringHash && len >= 32;
}

// Hashes up to 31 bytes 4 at a time into a 64-bit state. Each step takes 32 bits, spread over the state by a
// multiply, so a chosen word can't set the state: merging two states takes a 64-bit collision, not a solvable equation.
inline uint32_t wordHashShort(uint32_t seed, const char* str, size_t len)
{
    LUAU_ASSERT(len < 32);

    const uint64_t spread = 0xd6e8feb86659fd93ull;
    const uint64_t mult = 0x9e3779b97f4a7c15ull;
    uint64_t h = (uint64_t(seed) << 32) ^ len;

    if (len >= 4)
    {
        // whole words, then the last 4 bytes (overlapping when len isn't a multiple of 4)
        for (size_t i = 0; i + 4 < len; i += 4)
        {
            h ^= loadLe32(str + i) * spread;
            h *= mult;
            h ^= h >> 32;
        }

        h ^= loadLe32(str + len - 4) * spread;
    }
    else if (len > 0)
    {
        // bytes 0, len/2 and len-1 cover every byte of a 1 to 3 byte string
        h ^= ((uint32_t(uint8_t(str[0])) << 16) | (uint32_t(uint8_t(str[len >> 1])) << 8) | uint8_t(str[len - 1])) * spread;
    }

    h *= mult;
    h ^= h >> 32;
    h *= 0xbf58476d1ce4e5b9ull;
    h ^= h >> 29;

    return uint32_t(h);
}

// Strings of 32 bytes or more: luaS_hash's 12-byte blocks (lookup3 mix, loaded little-endian) while 32 or more remain,
// then the last 20 to 31 bytes by wordHashShort
inline uint32_t wordHash(const char* str, size_t len)
{
    uint32_t a = 0, b = 0;
    uint32_t h = uint32_t(len);

    while (len >= 32)
    {
#define rol(x, s) ((x >> s) | (x << (32 - s)))
#define mix(u, v, w) a ^= h, a -= rol(h, u), b ^= a, b -= rol(a, v), h ^= b, h -= rol(b, w)

        a += loadLe32(str);
        b += loadLe32(str + 4);
        h += loadLe32(str + 8);
        mix(14, 11, 25);
        str += 12;
        len -= 12;

#undef mix
#undef rol
    }

    return wordHashShort(h, str, len);
}

} // namespace Luau
