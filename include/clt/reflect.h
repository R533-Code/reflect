/*****************************************************************/ /**
 * @file   reflect.h
 * @brief  Provides macros and functions for static reflection.
 * 
 * While nobody likes macros, they are the only way to generate static
 * reflection at compile-time (while waiting for C++26's static
 * reflection).
 * The macros are needed to generate the info struct representing
 * the static informations.
 * FAQ:
 * 1 - Why is there two macros to get the informations?
 *   - (reflect_info_of and reflect_info_of_nt)
 * 1 > To reflect on namespaces and aliases, we need to have
 *   > informations about the entity stored somewhere.
 *   > A static constexpr variable that is partially specialized
 *   > cannot be specialized outside of its namespace...
 *   > We need to find another solution: functions!
 *   > Because of ADL, we can just create a function with the same
 *   > name, and depending on the type given to it, ADL will make
 *   > use of the function defined in the same namespace as the type.
 *   > Another advantage of this solution is that we can overload a
 *   > function with the same name for pointer types, and reference types,
 *   > thus obtaining a more generic solution that doesn't require macros
 *   > to output enormous amount of code.
 *   > As the types can be non-default constructible, and ADL works on pointers,
 *   > `__MetaInfo_Get` takes all the types as a pointer. This means that the
 *   > `__MetaInfo_Get` for `int` have a signature of `__MetaInfo_Get(int*)`.
 *   > There is still one problem, a function cannot take a namespace as
 *   > parameter. So all entities except type actually provide a static
 *   > constexpr of name `CONCAT(name, __MetaInfo_)` in the same namespace.
 *   > Thus, we get two macros to get informations:
 *   > - `reflect_info_of` that works for types using `__MetaInfo_Get`
 *   > - `reflect_info_of_nt` that works for all the rest.
 *   > There is also `reflect_info_of_const` for information over constants.
 * 
 * @author RPC
 * @date   November 2024
 *********************************************************************/
#ifndef HG_REFLECT__
#define HG_REFLECT__

#include <concepts>
#include <type_traits>
#include <cstdint>
#include <array>
#include <tuple>
#include <source_location>
#include <string_view>

#pragma region UGLY MACROS
/// @brief Concatenate internal (use __REFL_CC!!)
#define __REFL_CC2(x, y) x##y
/// @brief Transform a value to a string literal (use __REFL_STR!!)
#define __REFL_STR2(x) #x
/// @brief Transform a value to a string literal
#define __REFL_STR(x) __REFL_STR2(x)
/// @brief Pair of ()
#define __DETAILS__REFLECT_PARENS ()

/// @brief Helper for REFLECT_FOR_EACH_*
#define __DETAILS__REFLECT_EXPAND(...)                   \
  __DETAILS__REFLECT_EXPAND4(__DETAILS__REFLECT_EXPAND4( \
      __DETAILS__REFLECT_EXPAND4(__DETAILS__REFLECT_EXPAND4(__VA_ARGS__))))
/// @brief Helper for REFLECT_FOR_EACH_*
#define __DETAILS__REFLECT_EXPAND4(...)                  \
  __DETAILS__REFLECT_EXPAND3(__DETAILS__REFLECT_EXPAND3( \
      __DETAILS__REFLECT_EXPAND3(__DETAILS__REFLECT_EXPAND3(__VA_ARGS__))))
/// @brief Helper for REFLECT_FOR_EACH_*
#define __DETAILS__REFLECT_EXPAND3(...)                  \
  __DETAILS__REFLECT_EXPAND2(__DETAILS__REFLECT_EXPAND2( \
      __DETAILS__REFLECT_EXPAND2(__DETAILS__REFLECT_EXPAND2(__VA_ARGS__))))
/// @brief Helper for REFLECT_FOR_EACH_*
#define __DETAILS__REFLECT_EXPAND2(...)                  \
  __DETAILS__REFLECT_EXPAND1(__DETAILS__REFLECT_EXPAND1( \
      __DETAILS__REFLECT_EXPAND1(__DETAILS__REFLECT_EXPAND1(__VA_ARGS__))))
/// @brief Helper for REFLECT_FOR_EACH_*
#define __DETAILS__REFLECT_EXPAND1(...) __VA_ARGS__

/// @brief Helper for REFLECT_FOR_EACH_*
#define __DETAILS__REFLECT_FOR_EACH_HELPER_SYMBOL(macro, symbol, a1, ...) \
  macro(a1) __VA_OPT__(symbol) __VA_OPT__(                                \
      __DETAILS__REFLECT_FOR_EACH_AGAIN_SYMBOL __DETAILS__REFLECT_PARENS( \
          macro, symbol, __VA_ARGS__))
/// @brief Helper for REFLECT_FOR_EACH_*
#define __DETAILS__REFLECT_FOR_EACH_AGAIN_SYMBOL() \
  __DETAILS__REFLECT_FOR_EACH_HELPER_SYMBOL

/// @brief Helper for REFLECT_FOR_EACH_*
#define __DETAILS__REFLECT_FOR_EACH_HELPER_COMMA(macro, a1, ...)                    \
  macro(a1) __VA_OPT__(, )                                                          \
      __VA_OPT__(__DETAILS__REFLECT_FOR_EACH_AGAIN_COMMA __DETAILS__REFLECT_PARENS( \
          macro, __VA_ARGS__))
/// @brief Helper for REFLECT_FOR_EACH_*
#define __DETAILS__REFLECT_FOR_EACH_AGAIN_COMMA() \
  __DETAILS__REFLECT_FOR_EACH_HELPER_COMMA

/// @brief Helper for REFLECT_FOR_EACH_*
#define __DETAILS__REFLECT_FOR_EACH_HELPER(macro, a1, ...)                          \
  macro(a1) __VA_OPT__(__DETAILS__REFLECT_FOR_EACH_AGAIN __DETAILS__REFLECT_PARENS( \
      macro, __VA_ARGS__))
/// @brief Helper for REFLECT_FOR_EACH_*
#define __DETAILS__REFLECT_FOR_EACH_AGAIN() __DETAILS__REFLECT_FOR_EACH_HELPER

/// @brief Helper for REFLECT_FOR_EACH_*
#define __DETAILS__REFLECT_FOR_EACH_HELPER_1ARG(macro, arg, a1, ...)               \
  macro(arg, a1)                                                                   \
      __VA_OPT__(__DETAILS__REFLECT_FOR_EACH_AGAIN_1ARG __DETAILS__REFLECT_PARENS( \
          macro, arg, __VA_ARGS__))

/// @brief Helper for REFLECT_FOR_EACH_*
#define __DETAILS__REFLECT_FOR_EACH_AGAIN_1ARG() \
  __DETAILS__REFLECT_FOR_EACH_HELPER_1ARG

/// @brief Helper for REFLECT_FOR_EACH_*
#define __DETAILS__REFLECT_FOR_EACH_HELPER_2ARG(macro, arg1, arg2, a1, ...)        \
  macro(arg1, arg2, a1)                                                            \
      __VA_OPT__(__DETAILS__REFLECT_FOR_EACH_AGAIN_2ARG __DETAILS__REFLECT_PARENS( \
          macro, arg1, arg2, __VA_ARGS__))

/// @brief Helper for REFLECT_FOR_EACH_*
#define __DETAILS__REFLECT_FOR_EACH_AGAIN_2ARG() \
  __DETAILS__REFLECT_FOR_EACH_HELPER_2ARG

/// @brief Helper for REFLECT_FOR_EACH_*
#define __DETAILS__REFLECT_FOR_EACH_HELPER_3ARG(macro, arg1, arg2, arg3, a1, ...)  \
  macro(arg1, arg2, arg3, a1)                                                      \
      __VA_OPT__(__DETAILS__REFLECT_FOR_EACH_AGAIN_3ARG __DETAILS__REFLECT_PARENS( \
          macro, arg1, arg2, arg3, __VA_ARGS__))

/// @brief Helper for REFLECT_FOR_EACH_*
#define __DETAILS__REFLECT_FOR_EACH_AGAIN_3ARG() \
  __DETAILS__REFLECT_FOR_EACH_HELPER_3ARG

/// @brief Helper for REFLECT_FOR_EACH_*
#define __DETAILS__REFLECT_FOR_EACH_HELPER_4ARG(                                   \
    macro, arg1, arg2, arg3, arg4, a1, ...)                                        \
  macro(arg1, arg2, arg3, arg4, a1)                                                \
      __VA_OPT__(__DETAILS__REFLECT_FOR_EACH_AGAIN_4ARG __DETAILS__REFLECT_PARENS( \
          macro, arg1, arg2, arg3, arg4, __VA_ARGS__))

/// @brief Helper for REFLECT_FOR_EACH_*
#define __DETAILS__REFLECT_FOR_EACH_AGAIN_4ARG() \
  __DETAILS__REFLECT_FOR_EACH_HELPER_4ARG
#pragma endregion

#pragma region LESS UGLY MACROS

// Helpers for __REFL_deparen
#define __REFL_ISH(...)  __REFL_ISH __VA_ARGS__
#define __REFL_ESC(...)  __REFL_ESC_(__VA_ARGS__)
#define __REFL_ESC_(...) __REFL_VAN##__VA_ARGS__
#define __REFL_VAN__REFL_ISH

/// @brief Concatenate two values
#define __REFL_CC(x, y) __REFL_CC2(x, y)

/// @brief Extract the first value of a 2D tuple (use __REFL_2D_1!!)
#define __REFL_2D_1_(X, Y) X
/// @brief Extract the first value of a macro tuple
#define __REFL_2D_1(T) __REFL_2D_1_ T
/// @brief Extract the second value of a 2D tuple (use __REFL_2D_2!!)
#define __REFL_2D_2_(X, Y) Y
/// @brief Extract the second value of a macro tuple
#define __REFL_2D_2(T) __REFL_2D_2_ T

/// @brief Extract the first value of a 3D tuple (use __REFL_3D_1!!)
#define __REFL_3D_1_(X, Y, Z) X
/// @brief Extract the first value of a macro tuple
#define __REFL_3D_1(T) __REFL_3D_1_ T
/// @brief Extract the second value of a 3D tuple (use __REFL_3D_2!!)
#define __REFL_3D_2_(X, Y, Z) Y
/// @brief Extract the second value of a macro tuple
#define __REFL_3D_2(T) __REFL_3D_2_ T
/// @brief Extract the third value of a 3D tuple (use __REFL_3D_3!!)
#define __REFL_3D_3_(X, Y, Z) Z
/// @brief Extract the third value of a macro tuple
#define __REFL_3D_3(T) __REFL_3D_3_ T

/// @brief Applies 'macro' on each arguments
#define REFLECT_FOR_EACH(macro, ...)    \
  __VA_OPT__(__DETAILS__REFLECT_EXPAND( \
      __DETAILS__REFLECT_FOR_EACH_HELPER(macro, __VA_ARGS__)))

/// @brief Applies 'macro' on each arguments, separating all by 'symbol' (without ending with it).
#define REFLECT_FOR_EACH_SYMBOL(macro, symbol, ...) \
  __VA_OPT__(__DETAILS__REFLECT_EXPAND(             \
      __DETAILS__REFLECT_FOR_EACH_HELPER_SYMBOL(macro, symbol, __VA_ARGS__)))

/// @brief Applies 'macro' on each arguments, separating all by ',' (without ending with it).
/// This is VERY useful to expand function calls.
#define REFLECT_FOR_EACH_COMMA(macro, ...) \
  __VA_OPT__(__DETAILS__REFLECT_EXPAND(    \
      __DETAILS__REFLECT_FOR_EACH_HELPER_COMMA(macro, __VA_ARGS__)))

/// @brief Applies 'macro' on each arguments, invoking 'macro(arg1, arg2, arg3, arg4, <ARG>)'
#define REFLECT_FOR_EACH_4ARG(macro, arg1, arg2, arg3, arg4, ...)               \
  __VA_OPT__(__DETAILS__REFLECT_EXPAND(__DETAILS__REFLECT_FOR_EACH_HELPER_4ARG( \
      macro, arg1, arg2, arg3, arg4, __VA_ARGS__)))

/// @brief Applies 'macro' on each arguments, invoking 'macro(arg1, arg2, arg3, <ARG>)'
#define REFLECT_FOR_EACH_3ARG(macro, arg1, arg2, arg3, ...)                     \
  __VA_OPT__(__DETAILS__REFLECT_EXPAND(__DETAILS__REFLECT_FOR_EACH_HELPER_3ARG( \
      macro, arg1, arg2, arg3, __VA_ARGS__)))

/// @brief Applies 'macro' on each arguments, invoking 'macro(arg1, arg2, <ARG>)'
#define REFLECT_FOR_EACH_2ARG(macro, arg1, arg2, ...) \
  __VA_OPT__(__DETAILS__REFLECT_EXPAND(               \
      __DETAILS__REFLECT_FOR_EACH_HELPER_2ARG(macro, arg1, arg2, __VA_ARGS__)))

/// @brief Applies 'macro' on each arguments, invoking 'macro(arg, <ARG>)'
#define REFLECT_FOR_EACH_1ARG(macro, arg, ...) \
  __VA_OPT__(__DETAILS__REFLECT_EXPAND(        \
      __DETAILS__REFLECT_FOR_EACH_HELPER_1ARG(macro, arg, __VA_ARGS__)))

#pragma endregion

#pragma region DEFINE_MACROS
/// @brief If x is wrapped in parenthesis, removes them
#define __REFL_deparen(x) __REFL_ESC(__REFL_ISH x)
/// @brief Add at the end of a macro to require a semicolon
#define __REFL_macro_needs_semicolon() static_assert(true)

/// @brief Creates a using declaration.
/// @code{.cpp}
/// define_using(Char8, char8_t); // same as: using Char8 = char8_t
/// @endcode
#define define_using(name, value)                                             \
  using name                                         = __REFL_deparen(value); \
  static constexpr auto __REFL_CC(name, __MetaInfo_) = clt::meta::info<       \
      name, clt::meta::no_value,                                              \
      clt::meta::basic_info{                                                  \
          .kind    = clt::meta::Kind::_alias,                                 \
          .name_of = []() noexcept { return #name; },                         \
          .src     = []() noexcept { return std::source_location::current(); }},  \
      decltype(__MetaInfo_Get(static_cast<value*>(nullptr)))::current>        \
  {                                                                           \
  }

/// @brief Creates a typedef declaration.
/// @code{.cpp}
/// define_typedef(char8_t, Char8); // same as: using Char8 = char8_t
/// @endcode
#define define_typedef(value, name) define_using(name, value)

/// @brief Creates a namespace declaration.
/// @code{.cpp}
/// define_namespace(test) // same as: namespace test
/// {
///   // inside of namespace test
/// }
/// @endcode
#define define_namespace(name)                                           \
  static constexpr auto __REFL_CC(name, __MetaInfo_) = clt::meta::info<  \
      clt::meta::no_type, clt::meta::no_value,                           \
      clt::meta::basic_info{                                             \
          clt::meta::Kind::_namespace, []() noexcept { return #name; },  \
          []() noexcept { return std::source_location::current(); }}>{}; \
  namespace name

/// @brief Defines a primitive type (which does not have any members)
#define define_primitive_type(name)                                               \
  static_assert(                                                                  \
      !std::is_const_v<name> && !std::is_volatile_v<name>                         \
          && !std::is_reference_v<name>,                                          \
      "Argument of define_primitive_type must not be cvref qualified!");          \
  constexpr auto __MetaInfo_Reflectable(const name*) -> bool                      \
  {                                                                               \
    return true;                                                                  \
  }                                                                               \
  constexpr auto __MetaInfo_Get(const name*)                                      \
  {                                                                               \
    return clt::meta::info<                                                       \
        name, clt::meta::no_value,                                                \
        clt::meta::basic_info{                                                    \
            .kind    = clt::meta::Kind::_type,                                    \
            .name_of = []() noexcept { return #name; },                           \
            .src     = []() noexcept { return std::source_location::current(); }}>{}; \
  }

/// @brief Identity function (which returns its argument)
#define __REFL_identity(x) x
/// @brief Expands to 1
#define __REFL_one_plus(x) 1 +
/// @brief Expands an argument tuple (TYPE, NAME).
/// (TYPE, NAME) -> TYPE NAME
#define __REFL_fn_arguments_expansion(a) \
  __REFL_deparen(__REFL_2D_1(a)) __REFL_2D_2(a)
/// @brief Expands all the arguments one after the other.
/// This is used to expand the keywords (constexpr, static) => constexpr static
#define __REFL_expand_specifier(...) REFLECT_FOR_EACH(__REFL_identity, __VA_ARGS__)
/// @brief Converts a specifier keyword to the enum that represents them.
/// (constexpr) => Specifier::\_constexpr\_ |
#define __REFL_keyword_to_specifier(x) \
  (uint32_t) clt::meta::Specifier::__REFL_CC(__REFL_CC(_, x), _) |
/// @brief Converts specifier keywords to the enum that represents them.
/// (constexpr, static) => Specifier::\_constexpr\_ | Specifier::\_static\_ | Specifier::__End_marker
#define __REFL_or_specifier(...)                                           \
  (clt::meta::Specifier)(                                                  \
      REFLECT_FOR_EACH(__REFL_keyword_to_specifier, __VA_ARGS__)(uint32_t) \
          clt::meta::Specifier::__End_marker)
#define __REFL_arg_info(x)                                      \
  clt::meta::info<                                              \
      __REFL_2D_1(x), clt::meta::no_value,                      \
      clt::meta::basic_info{                                    \
          clt::meta::Kind::_var,                                \
          []() noexcept { return __REFL_STR(__REFL_2D_2(x)); }, \
          []() noexcept { return std::source_location::current(); }}>
#define __REFL_args_info(...) \
  std::tuple<REFLECT_FOR_EACH_COMMA(__REFL_arg_info, __VA_ARGS__)>

/// @brief Defines a function type.
/// @code{.cpp}
/// // The first pack can be empty but should still be written: ().
/// // The arguments must only be packs of 2.
/// define_fn((static, constexpr), int, sum, (int, a), (int, b))
/// {
///   return a + b;
/// }
/// @endcode
#define define_fn(pack, return_type, name, ...)                                    \
  __REFL_expand_specifier                                                          \
      pack /* as the pack is contained in () this will expand to a macro call */   \
          __REFL_deparen(return_type) name(                                        \
              REFLECT_FOR_EACH_COMMA(__REFL_fn_arguments_expansion, __VA_ARGS__)); \
  static constexpr auto __REFL_CC(name, __MetaInfo_) = clt::meta::info<            \
      decltype(name), &(name),                                                     \
      clt::meta::basic_info{                                                       \
          clt::meta::Kind::_fn, []() noexcept { return #name; },                   \
          []() noexcept { return std::source_location::current(); },               \
          (clt::meta::Specifier)(__REFL_or_specifier pack)},                       \
      clt::meta::basic_info{},                                                     \
      __REFL_args_info((return_type, <return>), __VA_ARGS__)>{};                   \
  __REFL_expand_specifier pack __REFL_deparen(return_type)                         \
      name(REFLECT_FOR_EACH_COMMA(__REFL_fn_arguments_expansion, __VA_ARGS__))

/// @brief Defines a variable
/// @code{.cpp}
/// // The first pack can be empty but should still be written: ().
/// // same as: static constexpr auto hello = 42;
/// define_var((static, constexpr), auto, hello, 42);
/// @endcode
#define define_var(pack, type, name, value)                                         \
  __REFL_expand_specifier                                                           \
      pack /* as the pack is contained in () this will expand to a macro call */    \
          __REFL_deparen(type) name                  = value;                       \
  static constexpr auto __REFL_CC(name, __MetaInfo_) = clt::meta::info<             \
      decltype(name), &(name),                                                      \
      clt::meta::basic_info{                                                        \
          clt::meta::Kind::_var, []() noexcept { return #name; }, []() noexcept     \
          { return std::source_location::current(); }, (__REFL_or_specifier pack)}> \
  {                                                                                 \
  }

/// @brief Reflect on a constant value
/// Due to a limitation of local classes, the value must be
/// a literal type that can be passed as a template parameter
#define reflect_info_of_const(value)                                          \
  clt::meta::info<                                                            \
      decltype(value), value,                                                 \
      clt::meta::basic_info{                                                  \
          clt::meta::Kind::_constant_value, []() noexcept { return #value; }, \
          []() noexcept { return std::source_location::current(); },          \
          clt::meta::Specifier::_constexpr_}>                                 \
  {                                                                           \
  }

// 0 -> non-type template
// 1 -> type template
// 2 -> non-type template pack
// 3 -> type template pack
#define __REFL_expand_template_argument(x) \
  __REFL_CC(__REFL_expand_template_argument, __REFL_3D_1(x))(x)
#define __REFL_expand_template_argument0(x) __REFL_3D_2(x) __REFL_3D_3(x)
#define __REFL_expand_template_argument1(x) __REFL_3D_2(x) __REFL_3D_3(x)
#define __REFL_expand_template_argument2(x) __REFL_3D_2(x)... __REFL_3D_3(x)
#define __REFL_expand_template_argument3(x) __REFL_3D_2(x)... __REFL_3D_3(x)
#define __REFL_expand_template_name(x) \
  __REFL_CC(__REFL_expand_template_name, __REFL_3D_1(x))(x)
#define __REFL_expand_template_name0(x) __REFL_3D_3(x)
#define __REFL_expand_template_name1(x) __REFL_3D_3(x)
#define __REFL_expand_template_name2(x) __REFL_3D_3(x)...
#define __REFL_expand_template_name3(x) __REFL_3D_3(x)...
#define __REFL_expand_template_pack(...) \
  REFLECT_FOR_EACH_COMMA(__REFL_expand_template_argument, __VA_ARGS__)
/// @brief Expand the names of template tuple pack
#define __REFL_expand_template_pack_name(...) \
  REFLECT_FOR_EACH_COMMA(__REFL_expand_template_name, __VA_ARGS__)
/// @brief Counts the number of argument of a macro.
/// This result in an expression not a single literal!
#define __REFL_count(...) REFLECT_FOR_EACH(__REFL_one_plus, __VA_ARGS__) 0
#define __REFL_expand_template_type_or_value(...) \
  REFLECT_FOR_EACH_COMMA(__REFL_3D_1, __VA_ARGS__)
#define __REFL_expand_substitute_argument(x) \
  __REFL_CC(__REFL_expand_substitute_argument, __REFL_3D_1(x))(x)
#define __REFL_expand_substitute_argument0(x) \
  clt::meta::meta_info auto __REFL_3D_3(x)
#define __REFL_expand_substitute_argument1(x) \
  clt::meta::meta_info auto __REFL_3D_3(x)
#define __REFL_expand_substitute_argument2(x) \
  clt::meta::meta_info auto... __REFL_3D_3(x)
#define __REFL_expand_substitute_argument3(x) \
  clt::meta::meta_info auto... __REFL_3D_3(x)
#define __REFL_expand_substitute_arguments(...) \
  REFLECT_FOR_EACH_COMMA(__REFL_expand_substitute_argument, __VA_ARGS__)
#define __REFL_expand_substitute_value0(x) decltype(__REFL_3D_3(x))::value
#define __REFL_expand_substitute_value1(x) typename decltype(__REFL_3D_3(x))::type
#define __REFL_expand_substitute_value2(x) typename decltype(__REFL_3D_3(x))::type...
#define __REFL_expand_substitute_value3(x) decltype(__REFL_3D_3(x))::value...
#define __REFL_expand_substitute_value(x) \
  __REFL_CC(__REFL_expand_substitute_value, __REFL_3D_1(x))(x)
#define __REFL_expand_substitute_values(...) \
  REFLECT_FOR_EACH_COMMA(__REFL_expand_substitute_value, __VA_ARGS__)
#define __REFL_expand_assert_value0(x)                                              \
  static_assert(                                                                    \
      !std::same_as<decltype(decltype(__REFL_3D_3(x))::value), clt::meta::no_type>, \
      "Expected an non-type template parameter!")
#define __REFL_expand_assert_value1(x)                                            \
  static_assert(                                                                  \
      !std::same_as<typename decltype(__REFL_3D_3(x))::type, clt::meta::no_type>, \
      "Expected a type template parameter!")
#define __REFL_expand_assert_value2(x)                                            \
  static_assert(                                                                  \
      (!std::same_as<typename decltype(__REFL_3D_3(x))::type, clt::meta::no_type> \
       && ...),                                                                   \
      "Expected a type template parameter pack!")
#define __REFL_expand_assert_value3(x)                                              \
  static_assert(                                                                    \
      (!std::same_as<decltype(decltype(__REFL_3D_3(x))::value), clt::meta::no_type> \
       && ...),                                                                     \
      "Expected a non-type template parameter pack!")
#define __REFL_expand_assert_value(x) \
  __REFL_CC(__REFL_expand_assert_value, __REFL_3D_1(x))(x);
#define __REFL_static_assert_parameters(...) \
  REFLECT_FOR_EACH(__REFL_expand_assert_value, __VA_ARGS__);

/// @brief Creates a non-type template parameter
#define reflect_template_value(type, name) (0, type, name)
/// @brief Creates a type template parameter
#define reflect_template_type(type, name) (1, type, name)
/// @brief Creates a non-type template parameter
#define reflect_variadic_template_type(type, name) (2, type, name)
/// @brief Creates a non-type template parameter pack
#define reflect_variadic_template_value(type, name) (3, type, name)

/// @brief Defines a templated variable
/// @code{.cpp}
/// // This the same as:
/// // template<typename T, typename b> static constexpr T Hello = (T(3.14) + b(10));
/// define_template_var(
///    (reflect_template_type(typename, T), reflect_template_type(typename, b)),
///    (static, constexpr), T, Hello, T(3.14) + b(10));
/// @endcode
#define define_template_var(template_pack, pack, var_type, name, init_value)       \
  template<__REFL_expand_template_pack template_pack>                              \
  __REFL_expand_specifier                                                          \
      pack /* as the pack is contained in () this will expand to a macro call */   \
          __REFL_deparen(var_type) name = init_value;                              \
  static constexpr struct __REFL_CC(name, __MetaInfo_Type)                         \
  {                                                                                \
    static constexpr bool __Is_Meta_Info            = true;                        \
    static constexpr size_t __Is_Template_Meta_Info = __REFL_count template_pack;  \
    static constexpr auto substitute(                                              \
        __REFL_expand_substitute_arguments template_pack) noexcept                 \
    {                                                                              \
      __REFL_static_assert_parameters template_pack constexpr auto ptr =           \
          value<__REFL_expand_substitute_values template_pack>;                    \
      return clt::meta::info<                                                      \
          std::remove_pointer_t<decltype(ptr)>, ptr, current.remove_template()>{}; \
    }                                                                              \
    template<__REFL_expand_template_pack template_pack>                            \
    using type = decltype(name<__REFL_expand_template_pack_name template_pack>);   \
    template<__REFL_expand_template_pack template_pack>                            \
    static constexpr auto value =                                                  \
        &name<__REFL_expand_template_pack_name template_pack>;                     \
    static constexpr clt::meta::basic_info current = {                             \
        clt::meta::Kind::_template_var, []() noexcept { return #name; },           \
        []() noexcept { return std::source_location::current(); },                 \
        (__REFL_or_specifier pack)};                                               \
  } __REFL_CC(name, __MetaInfo_) = {}

/// @brief Defines a templated using.
/// @code{.cpp}
/// // This the same as:
/// // template<typename T, size_t V> using Array = std::array<T, V>;
/// define_template_using(
///    (reflect_template_type(typename, T), reflect_template_value(size_t, V)),
///    Array, std::array<T, V>);
/// @endcode
#define define_template_using(template_pack, name, using_type)                    \
  template<__REFL_expand_template_pack template_pack>                             \
  using name = __REFL_deparen(using_type);                                        \
  static constexpr struct __REFL_CC(name, __MetaInfo_Type)                        \
  {                                                                               \
    static constexpr bool __Is_Meta_Info            = true;                       \
    static constexpr size_t __Is_Template_Meta_Info = __REFL_count template_pack; \
    static constexpr auto substitute(                                             \
        __REFL_expand_substitute_arguments template_pack) noexcept                \
    {                                                                             \
      using ptr = type<__REFL_expand_substitute_values template_pack>;            \
      return clt::meta::info<                                                     \
          ptr, clt::meta::no_value, current.remove_template()>{};                 \
    }                                                                             \
    template<__REFL_expand_template_pack template_pack>                           \
    using type = name<__REFL_expand_template_pack_name template_pack>;            \
    template<__REFL_expand_template_pack template_pack>                           \
    static constexpr auto value                    = clt::meta::no_value;         \
    static constexpr clt::meta::basic_info current = {                            \
        clt::meta::Kind::_template_alias, []() noexcept { return #name; },        \
        []() noexcept { return std::source_location::current(); }};               \
  } __REFL_CC(name, __MetaInfo_) = {}

/// @brief Defines a function type.
/// @code{.cpp}
/// // The first pack can be empty but should still be written: ().
/// // The arguments must only be packs of 2.
/// define_fn((static, constexpr), int, sum, (int, a), (int, b))
/// {
///   return a + b;
/// }
/// @endcode
#define define_template_fn(template_pack, pack, return_type, name, ...)            \
  template<__REFL_expand_template_pack template_pack>                              \
  __REFL_expand_specifier                                                          \
      pack /* as the pack is contained in () this will expand to a macro call */   \
          __REFL_deparen(return_type) name(                                        \
              REFLECT_FOR_EACH_COMMA(__REFL_fn_arguments_expansion, __VA_ARGS__)); \
  static constexpr struct __REFL_CC(name, __MetaInfo_Type)                         \
  {                                                                                \
    static constexpr bool __Is_Meta_Info            = true;                        \
    static constexpr size_t __Is_Template_Meta_Info = __REFL_count template_pack;  \
    static constexpr auto substitute(                                              \
        __REFL_expand_substitute_arguments template_pack) noexcept                 \
    {                                                                              \
      __REFL_static_assert_parameters template_pack constexpr auto ptr =           \
          value<__REFL_expand_substitute_values template_pack>;                    \
      return clt::meta::info<                                                      \
          std::remove_pointer_t<decltype(ptr)>, ptr, current.remove_template()>{}; \
    }                                                                              \
    template<__REFL_expand_template_pack template_pack>                            \
    using type = decltype(name<__REFL_expand_template_pack_name template_pack>);   \
    template<__REFL_expand_template_pack template_pack>                            \
    static constexpr auto value =                                                  \
        &name<__REFL_expand_template_pack_name template_pack>;                     \
    static constexpr clt::meta::basic_info current = {                             \
        clt::meta::Kind::_template_fn, []() noexcept { return #name; },            \
        []() noexcept { return std::source_location::current(); },                 \
        (__REFL_or_specifier pack)};                                               \
  } __REFL_CC(name, __MetaInfo_) = {};                                             \
  template<__REFL_expand_template_pack template_pack>                              \
  __REFL_expand_specifier pack __REFL_deparen(return_type)                         \
      name(REFLECT_FOR_EACH_COMMA(__REFL_fn_arguments_expansion, __VA_ARGS__))

/// @brief Returns the information of a type (or an alias)
#define reflect_info_of(name)                                       \
  (                                                                 \
      []()                                                          \
      {                                                             \
        static_assert(                                              \
            clt::meta::reflectable<std::remove_cvref_t<name>>,      \
            "Type does not provide informations to reflect upon!"); \
        return __MetaInfo_Get(static_cast<name*>(nullptr));         \
      }())

/// @brief Returns the type represented by a meta info
#define reflect_type_of(name) \
  std::remove_pointer_t<decltype([]<typename>() { \
      static_assert(clt::meta::meta_info<std::remove_cvref_t<decltype(name)>>, "Type does represent a meta info!"); \
      static_assert(!std::same_as<clt::meta::no_type, typename std::remove_cvref_t<decltype(name)>::type>, "meta info does not represent a type!"); \
      return std::add_pointer_t<typename std::remove_cvref_t<decltype(name)>::type>{}; }.template operator()<int>())>

/// @brief Returns the type of any other reflectable construct
#define reflect_info_of_nt(name) clt::meta::copy(__REFL_CC(name, __MetaInfo_))

#pragma endregion

namespace clt::meta
{
  template<typename T, typename... Ts>
  consteval auto tuple_without_1st(const std::tuple<T, Ts...>&)
  {
    return std::tuple<Ts...>{};
  }

  /// @brief Creates a copy of the value passed to the function.
  /// This is used to always return a copy of an info type inside of reflect_* macros.
  /// @param value The value to copy
  /// @return Copy of value
  consteval auto copy(const auto& value)
  {
    return value;
  }

  /// @brief Represents the absence of type
  struct no_type
  {
  };
  /// @brief Represents the absence of a value
  static constexpr no_type no_value = no_type{};

  /// @brief string view (of structural type).
  /// Simplified string view class with members public to allow
  /// usage in non-type template arguments.
  struct string_view
  {
    /// @brief The data
    const char* data_ = "";
    /// @brief The size
    size_t size_ = 0;

    constexpr string_view() noexcept                              = default;
    constexpr string_view(string_view&&) noexcept                 = default;
    constexpr string_view(const string_view&) noexcept            = default;
    constexpr string_view& operator=(string_view&&) noexcept      = default;
    constexpr string_view& operator=(const string_view&) noexcept = default;
    /// @brief Constructor
    /// @param ptr The pointer
    /// @param size The size
    constexpr string_view(const char* ptr, size_t size) noexcept
        : data_(ptr)
        , size_(size)
    {
    }
    /// @brief Constructor
    /// @tparam N The size of the literal
    /// @param str The string literal
    template<std::size_t N>
    constexpr string_view(const char (&str)[N])
        : data_(str)
        , size_(N - 1)
    {
    }
    /// @brief Constructor
    /// @param strv The string view to copy
    constexpr string_view(std::string_view strv)
        : data_(strv.data())
        , size_(strv.size())
    {
    }

    /// @brief Begin iterator
    /// @return Begin iterator
    constexpr auto begin() const noexcept { return data_; }
    /// @brief End iterator
    /// @return End iterator
    constexpr auto end() const noexcept { return data_ + size_; }
    /// @brief The data
    /// @return The data
    constexpr auto data() const noexcept { return data_; }
    /// @brief The size of the view
    /// @return The size of the view
    constexpr size_t size() const noexcept { return size_; }
    /// @brief Conversion to std::string_view
    constexpr operator std::string_view() const noexcept
    {
      return std::string_view{data_, size_};
    }
  };

  template<size_t multiply, char... Chrs>
  struct multiply_char
  {
    /// @brief The actual concatenation function
    /// @return Nul-terminated array of concatenated characters
    static constexpr auto impl() noexcept
    {
      constexpr std::size_t len = (sizeof...(Chrs) * multiply);
      std::array chrs           = {Chrs...};
      std::array<char, len + 1> arr{};
      for (size_t i = 0; i < len; i++)
        arr[i] = chrs.data()[i % chrs.size()];
      arr[len] = 0;
      return arr;
    }
    /// @brief Nul-terminated array of concatenated characters
    static constexpr auto arr = impl();
    /// @brief The result of concatenation
    static constexpr string_view value{arr.data(), arr.size() - 1};
  };

  /// @brief Repeats a string view N times
  /// @tparam Str The string view to repeat
  /// @tparam multiply The number of time to repeat it
  template<size_t multiply, const string_view& Str>
  struct multiply_strv
  {
    /// @brief The actual concatenation function
    /// @return Nul-terminated array of concatenated characters
    static constexpr auto impl() noexcept
    {
      constexpr std::size_t len = (Str.size() * multiply);
      std::array<char, len + 1> arr{};
      for (size_t i = 0; i < len; i++)
        arr[i] = Str.data()[i % Str.size()];
      arr[len] = 0;
      return arr;
    }
    /// @brief Nul-terminated array of concatenated characters
    static constexpr auto arr = impl();
    /// @brief The result of concatenation
    static constexpr string_view value{arr.data(), arr.size() - 1};
  };

  /// @brief Concatenates string views at compile-time
  /// @tparam ...Strs The string views to concatenate
  template<const string_view&... Strs>
  struct join_strv
  {
    /// @brief The actual concatenation function
    /// @return Nul-terminated array of concatenated characters
    static constexpr auto impl() noexcept
    {
      constexpr std::size_t len = (Strs.size() + ... + 0);
      std::array<char, len + 1> arr{};
      auto append = [i = 0, &arr](auto const& s) mutable
      {
        for (auto c : s)
          arr[i++] = c;
      };
      (append(Strs), ...);
      arr[len] = 0;
      return arr;
    }
    /// @brief Nul-terminated array of concatenated characters
    static constexpr auto arr = impl();
    /// @brief The result of concatenation
    static constexpr string_view value{arr.data(), arr.size() - 1};
  };

  /// @brief The kind of the reflection
  enum class Kind : uint32_t
  {
    _error,

    /// @brief Non-templated variable
    _var,
    /// @brief Non-templated using
    _alias,
    /// @brief Non-templated function
    _fn,
    /// @brief Non-templated method
    _method,
    /// @brief Non-templated type
    _type,
    /// @brief Static Data Member
    _sdm,
    /// @brief Templated variable
    _template_var,
    /// @brief Templated using
    _template_alias,
    /// @brief Templated function
    _template_fn,
    /// @brief Templated method
    _template_method,
    /// @brief Templated type
    _template_type,
    /// @brief Templated static data member
    _template_sdm,
    /// @brief Non-Static Data Member
    _nsdm,
    /// @brief Constant Value
    _constant_value,
    /// @brief Namespace Description
    _namespace,
    __End_marker
  };

  /// @brief Remove template from kind.
  /// This is the same effect as _template(.*) -> $1.
  /// @param kind The kind from which to remove _template
  /// @return __End_marker if the kind did not represent a template or the result
  constexpr Kind kind_remove_template(Kind kind) noexcept
  {
    using enum clt::meta::Kind;
    switch (kind)
    {
    case _template_method:
      return _method;
    case _template_var:
      return _var;
    case _template_alias:
      return _alias;
    case _template_fn:
      return _fn;
    case _template_sdm:
      return _sdm;
    case _template_type:
      return _type;
    default:
      return __End_marker;
    }
  }

  /// @brief The visibility of the reflected object
  enum class Visibility : uint8_t
  {
    _public_     = 0,
    _protected_  = 1,
    _private_    = 2,
    __End_marker = 3,
  };

  /// @brief The specifiers applied to the object
  enum class Specifier : uint32_t
  {
    _inline_       = 1 << 0,
    _static_       = 1 << 1,
    _constexpr_    = 1 << 2,
    _thread_local_ = 1 << 3,
    _virtual_      = 1 << 4,
    _deleted_      = 1 << 5,
    _default_      = 1 << 6,
    _explicit_     = 1 << 7,
    _override_     = 1 << 8,
    __End_marker   = 1 << 9,
  };

  /// @brief Represents the basic informations of a reflected type.
  /// These informations do not give access to the underlying type
  /// reflected on, neither the address/value of that reflected value.
  struct basic_info
  {
    using str_producer_t = const char* (*)() noexcept;
    using loc_producer_t = std::source_location (*)() noexcept;

    /// @brief The kind of the reflection
    Kind kind = Kind::_error;
    /// @brief The name of the reflection (unqualified)
    str_producer_t name_of = nullptr;
    /// @brief The source location of the reflection
    loc_producer_t src = nullptr;
    /// @brief The specifiers or __End_marker if none
    Specifier specifier = Specifier::__End_marker;
    /// @brief The visibility or __End_marker if none
    Visibility visibility = Visibility::__End_marker;

    /// @brief Returns a copy of these informations with kind = kind_remove_template(kind)
    /// @return Copy with kind = kind_remove_template(kind)
    constexpr basic_info remove_template() const noexcept
    {
      return {kind_remove_template(kind), name_of, src, specifier, visibility};
    }
  };

  /// @brief Result of reflection over anything.
  /// @tparam T The type reflected on (or no_type)
  /// @tparam V The address/value reflected on (or no_value)
  template<
      typename T, auto V, basic_info CURRENT, basic_info ALIAS = basic_info{},
      typename ARGS = no_type>
  struct info
  {
    /// @brief The type represented by the info or 'no_type'
    using type = T;
    /// @brief The value represented by the info or 'no_value'
    static constexpr auto value = V;
    /// @brief The current informations
    static constexpr auto current = CURRENT;
    /// @brief This field is only useful if
    static constexpr auto alias_info = ALIAS;
    /// @brief The arguments informations for functions
    using arguments_type = ARGS;
    /// @brief Helper to detect a valid info
    static constexpr bool __Is_Meta_Info = true;
  };

  /// @brief Represents an 'info' with specific types/values
  template<typename T>
  concept meta_info = std::convertible_to<decltype(T::current), basic_info>
                      && std::convertible_to<decltype(T::__Is_Meta_Info), bool>;

  /// @brief Check if T without its cv ref qualifiers is a meta_info
  template<typename T>
  concept meta_info_ref = meta_info<std::remove_cvref_t<T>>;

  /// @brief Represents an 'info' with specific types/values
  template<typename T>
  concept template_meta_info = requires {
    { T::current } -> std::convertible_to<basic_info>;
    { T::__Is_Meta_Info } -> std::convertible_to<bool>;
    { T::__Is_Template_Meta_Info } -> std::convertible_to<size_t>;
  };

  /// @brief Check if T without its cv ref qualifiers is a meta_info
  template<typename T>
  concept template_meta_info_ref = template_meta_info<std::remove_cvref_t<T>>;

  consteval auto is_public(meta_info_ref auto r) noexcept -> bool;
  consteval auto is_protected(meta_info_ref auto r) noexcept -> bool;
  consteval auto is_private(meta_info_ref auto r) noexcept -> bool;
  consteval auto is_accessible(meta_info_ref auto r) noexcept -> bool;
  consteval auto is_virtual(meta_info_ref auto r) noexcept -> bool;
  consteval auto is_deleted(meta_info_ref auto entity) noexcept -> bool;
  consteval auto is_defaulted(meta_info_ref auto entity) noexcept -> bool;
  consteval auto is_explicit(meta_info_ref auto entity) noexcept -> bool;
  consteval auto is_override(meta_info_ref auto entity) noexcept -> bool;
  consteval auto is_pure_virtual(meta_info_ref auto entity) noexcept -> bool;
  /// @brief Check if the entity is marked constexpr.
  /// @param entity The entity (representing a function or variable)
  /// @return True if the entity is marked constexpr
  consteval auto is_constexpr(meta_info_ref auto entity) noexcept -> bool
  {
    static_assert(
        is_variable(entity) || is_function(entity),
        "Expected variable or function information!");
    return (uint32_t) decltype(entity)::current.specifier
           & (uint32_t)Specifier::_constexpr_;
  }
  /// @brief Check if the entity has static storage duration.
  /// @param r The entity (representing a variable)
  /// @return True if the entity has static storage duration
  consteval auto has_static_storage_duration(meta_info_ref auto r) noexcept -> bool
  {
    static_assert(is_variable(r), "Expected variable information!");
    return (uint32_t) decltype(r)::current.specifier & (uint32_t)Specifier::_static_;
  }
  /// @brief Check if the entity has thread local storage duration.
  /// @param r The entity (representing a variable)
  /// @return True if the entity has thread local storage duration
  consteval auto has_thread_local_storage_duration(meta_info_ref auto r) noexcept
      -> bool
  {
    static_assert(is_variable(r), "Expected variable information!");
    return (uint32_t) decltype(r)::current.specifier
           & (uint32_t)Specifier::_thread_local_;
  }

  //constexpr auto is_base(meta_info_ref auto entity) -> bool;
  consteval auto is_nsdm(meta_info_ref auto entity) noexcept -> bool
  {
    return decltype(entity)::current.kind == Kind::_nsdm;
  }
  consteval auto is_sdm(meta_info_ref auto entity) noexcept -> bool
  {
    return decltype(entity)::current.kind == Kind::_sdm;
  }
  consteval auto is_namespace(meta_info_ref auto entity) noexcept -> bool
  {
    return decltype(entity)::current.kind == Kind::_namespace;
  }
  consteval auto is_value(meta_info_ref auto entity) noexcept -> bool
  {
    return decltype(entity)::current.kind == Kind::_constant_value;
  }
  consteval auto is_function(meta_info_ref auto entity) noexcept -> bool
  {
    return decltype(entity)::current.kind == Kind::_fn;
  }
  consteval auto is_method(meta_info_ref auto entity) noexcept -> bool
  {
    return decltype(entity)::current.kind == Kind::_method;
  }
  consteval auto is_static(meta_info_ref auto entity) noexcept -> bool
  {
    return decltype(entity)::current.kind == Kind::_fn;
  }
  consteval auto is_variable(meta_info_ref auto entity) noexcept -> bool
  {
    return decltype(entity)::current.kind == Kind::_var;
  }
  consteval auto is_type(meta_info_ref auto entity) noexcept -> bool
  {
    return decltype(entity)::current.kind == Kind::_type;
  }
  consteval auto is_alias(meta_info_ref auto entity) noexcept -> bool
  {
    return decltype(entity)::current.kind == Kind::_alias;
  }
  consteval auto is_template(meta_info_ref auto entity) noexcept -> bool
  {
    using enum clt::meta::Kind;
    return decltype(entity)::current.kind == _template_fn
           || decltype(entity)::current.kind == _template_var
           || decltype(entity)::current.kind == _template_type
           || decltype(entity)::current.kind == _template_alias
           || decltype(entity)::current.kind == _template_sdm;
  }
  consteval auto is_method_template(meta_info_ref auto entity) noexcept -> bool
  {
    return decltype(entity)::current.kind == Kind::_template_method;
  }
  consteval auto is_function_template(meta_info_ref auto entity) noexcept -> bool
  {
    return decltype(entity)::current.kind == Kind::_template_fn;
  }
  consteval auto is_sdm_template(meta_info_ref auto entity) noexcept -> bool
  {
    return decltype(entity)::current.kind == Kind::_template_sdm;
  }
  consteval auto is_variable_template(meta_info_ref auto entity) noexcept -> bool
  {
    return decltype(entity)::current.kind == Kind::_template_var;
  }
  consteval auto is_class_template(meta_info_ref auto entity) noexcept -> bool
  {
    return decltype(entity)::current.kind == Kind::_template_type;
  }
  consteval auto is_alias_template(meta_info_ref auto entity) noexcept -> bool
  {
    return decltype(entity)::current.kind == Kind::_template_alias;
  }
  consteval auto has_template_arguments(meta_info_ref auto r) noexcept -> bool;

  /// @brief Returns the name of the entity
  /// @param entity The entity
  /// @return The name of the entity
  constexpr auto name_of(meta_info_ref auto entity) noexcept -> std::string_view
  {
    return decltype(entity)::current.name_of();
  }

  /// @brief Returns the source location of an entity
  /// @param entity The entity
  /// @return The source location of the entity
  constexpr auto source_location_of(meta_info_ref auto entity) noexcept
      -> std::source_location
  {
    return decltype(entity)::current.src();
  }

  /// @brief If r designates an alias, designates the underlying entity, else produces r.
  /// @param r The info for which to extract the value
  /// @return If is_alias(r), the aliased type, else r
  consteval auto entity_of(meta_info_ref auto r) noexcept
  {
    if constexpr (!is_alias(r))
      return r;
    else
      return info<
          typename decltype(r)::type, decltype(r)::value, decltype(r)::alias_info>{};
  }

  /// @brief Returns the type represented by an info.
  /// This is the same nearly the same as reflect_type_of macro.
  template<meta_info_ref T>
  using type_of = std::remove_pointer_t<decltype([]<typename>() {
      static_assert(clt::meta::meta_info<std::remove_cvref_t<T>>, "Type does represent a meta info!");
      static_assert(!std::same_as<clt::meta::no_type, typename std::remove_cvref_t<T>::type>, "meta info does not represent a type!");
      return std::add_pointer_t<typename std::remove_cvref_t<T>::type>{}; }.template operator()<int>())>;

  /// @brief Instantiates a templated value using 'with'
  /// @tparam ...With The argument pack
  /// @param templ The template information to instantiate
  /// @param ...with The argument pack of information to use to instantiate
  /// @return Information of the instantiated type
  template<meta_info_ref... With>
  constexpr auto substitute(template_meta_info_ref auto templ, With... with) noexcept
  {
    return decltype(templ)::substitute(with...);
  }

  /// @brief Returns a reference to the value represented by a variable or function
  /// @param var_or_func The variable or function to which to obtain a reference
  /// @return Reference to the variable or function
  constexpr auto& entity_ref(meta_info_ref auto var_or_func) noexcept
  {
    static_assert(
        is_variable(var_or_func) || is_function(var_or_func),
        "Expected variable or function information!");
    return *decltype(var_or_func)::value;
  }

  /// @brief Returns a tuple of information representing the arguments of a function
  /// @param func The function's information
  /// @return Tuple of the information representing the arguments of a function
  consteval auto arguments_of(meta_info_ref auto func) noexcept
  {
    static_assert(is_function(func), "Expected function information!");
    return tuple_without_1st(typename decltype(func)::arguments_type{});
  }
  /// @brief Returns the information representing the return type of a function
  /// @param func The function's information
  /// @return Information representing the return of a function
  consteval auto return_of(meta_info_ref auto func) noexcept
  {
    static_assert(is_function(func), "Expected function information!");
    return std::get<0>(typename decltype(func)::arguments_type{});
  }

  /// @brief Returns the value of a constant value
  /// @param constant_expr The constant value
  /// @return The value
  consteval auto value_of(meta_info_ref auto constant_expr) noexcept
  {
    static_assert(
        is_value(constant_expr),
        "Expected a constant value (created using reflect_info_of_const)!");
    return decltype(constant_expr)::value;
  }
  constexpr auto pointer_to_member(meta_info_ref auto member) noexcept;

  constexpr auto offset_of(meta_info_ref auto entity) noexcept -> size_t;
  constexpr auto size_of(meta_info_ref auto entity) noexcept -> size_t;

  template<typename>
  constexpr bool always_false = false;
} // namespace clt::meta

define_primitive_type(void);
define_primitive_type(bool);
define_primitive_type(char);
define_primitive_type(wchar_t);
define_primitive_type(char8_t);
define_primitive_type(char16_t);
define_primitive_type(char32_t);
define_primitive_type(int8_t);
define_primitive_type(int16_t);
define_primitive_type(int32_t);
define_primitive_type(int64_t);
define_primitive_type(uint8_t);
define_primitive_type(uint16_t);
define_primitive_type(uint32_t);
define_primitive_type(uint64_t);
define_primitive_type(float);
define_primitive_type(double);
define_primitive_type(long double);

/// @brief By default, all types are not reflectable.
/// This is replaced by ADL __MetaInfo_Reflectable that are not templated
/// per type (as overloads take priority over templates).
/// @tparam Ty The type
/// @return Always false
template<typename Ty>
constexpr auto __MetaInfo_Reflectable(Ty*) -> bool
{
  return false;
}

/****************************************
|           TYPE UTILITIES              |
****************************************/
namespace clt::meta
{
  /// @brief Removes all pointer qualifications from a type (and counts them)
  /// @tparam T The type from which to remove the pointers
  template<typename T>
  struct remove_all_pointers
      : std::conditional_t<
            std::is_pointer_v<T>, remove_all_pointers<std::remove_pointer_t<T>>,
            std::type_identity<T>>
  {
    static consteval size_t _Get_Value()
    {
      // We need to use if constexpr to stop instantiating
      if constexpr (std::is_pointer_v<T>)
        return 1 + remove_all_pointers<std::remove_pointer_t<T>>::value;
      return 0;
    }

    static constexpr size_t value = _Get_Value();
  };

  /// @brief Short-hand of remove_all_pointers<>::type
  /// @tparam T The type
  template<typename T>
  using remove_all_pointers_t = typename remove_all_pointers<T>::type;

  /// @brief Adds N pointer qualifications to a type
  /// @tparam T The type to which to add pointers
  /// @tparam VALUE The number of pointers to add
  template<typename T, size_t VALUE>
  struct add_N_pointers
      : std::conditional_t<
            (VALUE != 0), add_N_pointers<std::add_pointer_t<T>, VALUE - 1>,
            std::type_identity<T>>
  {
    static constexpr size_t value = VALUE;
  };

  /// @brief Short-hand of add_N_pointers<>::type
  /// @tparam T The type
  /// @tparam VALUE The value
  template<typename T, size_t VALUE>
  using add_N_pointers_t = typename add_N_pointers<T, VALUE>::type;

  constexpr auto is_reflectable = []<typename T>
  {
    return __MetaInfo_Reflectable(
        std::add_pointer_t<
            std::add_const_t<std::remove_cvref_t<remove_all_pointers_t<T>>>>{});
  };

  template<typename T>
  concept reflectable = is_reflectable.template operator()<T>();

  template<typename T>
  concept pointer_reflectable = reflectable<T> && (std::is_pointer_v<T>);

  /// @brief Computes the string length of a NUL-terminated string
  /// @param str The string whose size to return
  /// @return The string length (not including the NUL-terminator)
  consteval size_t const_strlen(const char* str) noexcept
  {
    auto cpy = str;
    while (*str != '\0')
      ++str;
    return str - cpy;
  }
} // namespace clt::meta

/// @brief Static storage used by __MetaInfo_Get for pointer types. Do not use elsewhere!
/// This would not be needed in C++23 as static constexpr inside of functions will
/// be valid.
/// @tparam T The type without pointers
template<typename T>
static constexpr auto __MetaInfo_Get_static =
    __MetaInfo_Get(std::add_pointer_t<std::add_const_t<typename T::type>>{});
template<typename T>
static constexpr auto __MetaInfo_GetNameArray = []()
{
  using type            = decltype(__MetaInfo_Get(
      std::add_pointer_t<std::add_const_t<typename T::type>>{}));
  constexpr size_t size = clt::meta::const_strlen(type::current.name_of());
  std::array<char, size + 1> array;
  for (size_t i = 0; i < size; i++)
    array[i] = type::current.name_of()[i];
  array[size] = '\0';
  return array;
}();
template<typename T>
static constexpr clt::meta::string_view __MetaInfo_GetNameOf = {
    __MetaInfo_GetNameArray<T>.data(), __MetaInfo_GetNameArray<T>.size() - 1};

/// @brief Returns the meta information of a pointer to a type with informations.
/// This needs to be in the global namespace to be the last functions checked
/// after ADL.
/// The functions __MetaInfo_Get always take a pointer to a type to avoid
/// having to default construct the object.
/// @tparam Ty The type (which is a N pointer indirection to a reflectable type)
/// @return Information describing that type
template<clt::meta::pointer_reflectable Ty>
constexpr auto __MetaInfo_Get(Ty)
{
  using namespace clt::meta;
  using pointer_c = remove_all_pointers<Ty>;

  using type_ = typename decltype(__MetaInfo_Get_static<pointer_c>)::type;
  constexpr auto& name_array = __MetaInfo_GetNameOf<pointer_c>;
  return info<
      add_N_pointers_t<typename pointer_c::type, pointer_c::value - 1>,
      clt::meta::no_value,
      basic_info{
          .kind = Kind::_type,
          // Add missing pointers to type name
          .name_of =
              []() noexcept
          {
            return join_strv<
                       __MetaInfo_GetNameOf<pointer_c>,
                       multiply_char<pointer_c::value - 1, '*'>::value>::value
                .data();
          },
          .src = decltype(__MetaInfo_Get_static<pointer_c>)::current.src}>{};
}

/// @brief static_assert with an error.
/// This is the most general overload, which means it gets called after all
/// the other alternatives.
/// @tparam Ty The type (which does not provide informations)
/// @return No return
template<typename Ty>
constexpr auto __MetaInfo_Get(Ty)
    -> clt::meta::info<Ty, clt::meta::no_value, clt::meta::basic_info{}>
{
  static_assert(
      clt::meta::always_false<Ty>,
      "Type does not provide informations to reflect upon!");
  return {};
}

#pragma region TESTS
// If REFLECT_NO_SELF_TEST is not defined, some checks are run
// to ensure that the library is working correctly.
#ifndef REFLECT_NO_SELF_TEST

define_namespace(_Test_Reflect)
{
  //////////////////////////////
  // NAMESPACE:
  //////////////////////////////
  static_assert(
      clt::meta::name_of(reflect_info_of_nt(_Test_Reflect)) == "_Test_Reflect",
      "name_of namespace failed!");
  static_assert(
      clt::meta::is_namespace(reflect_info_of_nt(_Test_Reflect)),
      "is_namespace failed!");

  //////////////////////////////
  // FUNCTION:
  //////////////////////////////
  define_fn((inline), void, test_inside_function)
  {
  }
  static_assert(
      clt::meta::name_of(reflect_info_of_nt(_Test_Reflect::test_inside_function))
          == "test_inside_function",
      "name_of function failed!");
  static_assert(
      &clt::meta::entity_ref(reflect_info_of_nt(test_inside_function))
          == &test_inside_function,
      "entity_ref function failed!");
  static_assert(
      clt::meta::is_function(reflect_info_of_nt(test_inside_function)),
      "is_function function failed!");

  //////////////////////////////
  // VARIABLE:
  //////////////////////////////
  define_var((static, constexpr), int, test_variable, 10);
  static_assert(
      clt::meta::name_of(reflect_info_of_nt(_Test_Reflect::test_variable))
          == "test_variable",
      "name_of variable failed!");
  static_assert(
      std::same_as<
          decltype(clt::meta::source_location_of(
              reflect_info_of_nt(_Test_Reflect::test_variable))),
          std::source_location>,
      "source_location_of variable failed!");
  static_assert(
      &clt::meta::entity_ref(reflect_info_of_nt(test_variable)) == &test_variable,
      "entity_ref variable failed!");
  static_assert(
      clt::meta::is_variable(reflect_info_of_nt(test_variable)),
      "is_variable failed!");

  //////////////////////////////
  // PRIMITIVE TYPE:
  //////////////////////////////
  static_assert(
      std::same_as<int, reflect_type_of(reflect_info_of(int))>,
      "reflect_type_of primitive type failed!");
  static_assert(
      clt::meta::name_of(reflect_info_of(int32_t)) == "int32_t",
      "name_of primitive type failed!");
  static_assert(
      std::same_as<
          decltype(clt::meta::source_location_of(reflect_info_of(int32_t))),
          std::source_location>,
      "source_location_of primitive type failed!");

  //////////////////////////////
  // VARIABLE TEMPLATE:
  //////////////////////////////
  define_template_var(
      (reflect_template_type(typename, T), reflect_template_value(int, V)),
      (static, constexpr), T, test_template_variable, T(3.14) + T(V));
  static_assert(
      clt::meta::name_of(reflect_info_of_nt(_Test_Reflect::test_template_variable))
          == "test_template_variable",
      "name_of variable template failed!");
  static_assert(
      std::same_as<
          decltype(clt::meta::source_location_of(
              reflect_info_of_nt(_Test_Reflect::test_template_variable))),
          std::source_location>,
      "source_location_of variable template failed!");
  static_assert(
      clt::meta::is_variable_template(reflect_info_of_nt(test_template_variable)),
      "is_variable_template failed!");
  static_assert(
      &clt::meta::entity_ref(clt::meta::substitute(
          reflect_info_of_nt(test_template_variable), reflect_info_of_const(10),
          reflect_info_of_const(10)))
          == &test_template_variable<int, 10>,
      "entity_ref of substitute failed!");
  static_assert(
      clt::meta::entity_ref(clt::meta::substitute(
          reflect_info_of_nt(test_template_variable), reflect_info_of(int),
          reflect_info_of_const(10)))
          == 13,
      "entity_ref of substitute failed!");
  static_assert(
      clt::meta::is_variable(clt::meta::substitute(
          reflect_info_of_nt(test_template_variable), reflect_info_of(int),
          reflect_info_of_const(10))),
      "is_variable of substitute failed!");
  //////////////////////////////
  // FUNCTION TEMPLATE:
  //////////////////////////////
  define_template_fn(
      (reflect_template_type(typename, T), reflect_variadic_template_value(int, b)),
      (static, constexpr), T, sum)
  {
    return (T)(0 + ... + b);
  }
  static_assert(
      clt::meta::name_of(reflect_info_of_nt(_Test_Reflect::sum)) == "sum",
      "name_of funtion template failed!");
  static_assert(
      std::same_as<
          decltype(clt::meta::source_location_of(
              reflect_info_of_nt(_Test_Reflect::sum))),
          std::source_location>,
      "source_location_of function template failed!");
  static_assert(
      clt::meta::is_function_template(reflect_info_of_nt(sum)),
      "is_function_template failed!");
  static_assert(
      &clt::meta::entity_ref(clt::meta::substitute(
          reflect_info_of_nt(sum), reflect_info_of(int), reflect_info_of_const(10),
          reflect_info_of_const(10)))
          == &sum<int, 10, 10>,
      "entity_ref of substitute failed!");
  static_assert(
      clt::meta::entity_ref(clt::meta::substitute(
          reflect_info_of_nt(sum), reflect_info_of(int), reflect_info_of_const(10),
          reflect_info_of_const(10)))()
          == 20,
      "entity_ref of substitute failed!");
  static_assert(
      clt::meta::is_function(clt::meta::substitute(
          reflect_info_of_nt(sum), reflect_info_of(int), reflect_info_of_const(10),
          reflect_info_of_const(10))),
      "is_function of substitute failed!");

} // namespace _Test_Reflect

#endif // SELF_TEST_REFLECT
#pragma endregion

namespace clt::meta
{
  // PREDEFINED META FUNCTIONS:

  namespace details
  {
    template<meta_info_ref... Ts, size_t... Index>
    constexpr auto tupled(
        meta_info_ref auto fn, const std::tuple<Ts...>& tuple,
        std::index_sequence<Index...>) noexcept
    {
      using Info = decltype(fn);
      return +[](const std::tuple<type_of<Ts>...>& tuple)
      { return entity_ref(Info{})(std::get<Index>(tuple)...); };
    }

    template<typename Callable, meta_info... Args, size_t... Index>
    constexpr void for_each(
        const std::tuple<Args...>& arg, Callable&& callable,
        std::index_sequence<Index...>)
    {
      (callable(std::get<Index>(arg)), ...);
    }
  } // namespace details

  /// @brief Returns the same function as 'fn' with the difference that all the arguments are passed as
  /// a single tuple.
  /// @param fn The function information from which to generate the new function
  /// @return Function that takes all the arguments
  constexpr auto tupled(meta_info_ref auto fn) noexcept
  {
    static_assert(is_function(fn), "Expected a function!");
    constexpr auto tuple = arguments_of(fn);
    return details::tupled(
        fn, tuple, std::make_index_sequence<std::tuple_size_v<decltype(tuple)>>{});
  }

  /// @brief Applies a lambda for each information in a tuple
  /// @tparam Callable The lambda to apply on each members of the tuple
  /// @tparam ...Args The tuple arguments
  /// @param tuple The tuple whose members to pass to 'callable'
  /// @param callable The lambda to apply on each member of 'tuple'
  template<typename Callable, meta_info... Args>
  constexpr void for_each(const std::tuple<Args...>& tuple, Callable&& callable)
  {
    details::for_each(
        tuple, std::forward<Callable>(callable),
        std::make_index_sequence<sizeof...(Args)>{});
  }
} // namespace clt::meta

#endif // !HG_REFLECT__