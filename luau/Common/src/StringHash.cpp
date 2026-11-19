// This file is part of the Luau programming language and is licensed under MIT License; see LICENSE.txt for details
#include "Luau/StringHash.h"

// In Common, which both the VM and the compiler link, so that each can read it (see StringHash.h)
LUAU_DYNAMIC_FASTFLAGVARIABLE(LuauShortStringHash, true)
LUAU_DYNAMIC_FASTFLAGVARIABLE(LuauLongStringHash, true)
