# Reflect:
A macro-based static reflection library for C++20.
This solution for static reflection is intrusive to generate the static information,
but the result can be used with normal functions that match the interface of `P2996R0`
with additional support for reflection on functions.

## Supported Compilers:
Due to the heavy metaprogramming used in this library, a C++20 compliant compiler is needed.
Minimum Requirements: `GCC 13.2` or `clang 18.1.0` or `MSVC v19.34` (with `/Zc:preprocessor`).