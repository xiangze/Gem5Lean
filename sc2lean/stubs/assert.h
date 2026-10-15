// sc2lean: <cassert> の最小スタブ
#pragma once
namespace sc_core { void sc_assert_(bool); }
#define assert(x) ::sc_core::sc_assert_(x)
