#include "reflect.h"
#include <iostream>

using namespace clt::meta;

define_namespace(test)
{
  struct A
  {
  };
  define_primitive_type(A);
}

define_fn((static, constexpr), int, hello, (int, a), (int, b))
{
  return a + b;
}

#define PRINT_NAME(name) \
  std::cout << #name << ": " << name_of(reflect_info_of(name)) << '\n'
#define PRINT(name) std::cout << #name << ": " << (name) << '\n'

define_template_var(
    (reflect_template_type(typename, T), reflect_template_value(int, b)),
    (static, constexpr), T, Hello, T(3.14) + T(b));

int main()
{

  define_var((static), int, d, 10);
  define_using(ahello, long double);

  PRINT(name_of(reflect_info_of_nt(Hello)));
  constexpr auto a1 =
      substitute(reflect_info_of_nt(Hello), reflect_info_of(int), reflect_info_of_const(10));

  constexpr auto info = reflect_info_of_nt(hello);
  using a = reflect_type_of(info);
  PRINT(name_of(entity_of(reflect_info_of(ahello*****))));
  std::cout << (entity_ref(info)(10, 20));
  PRINT(name_of(info));
  constexpr auto info2 = reflect_info_of_nt(test);
  PRINT_NAME(ahello);
}