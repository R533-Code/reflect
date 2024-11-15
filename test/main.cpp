#include <clt/reflect.h>
#include <iostream>
#include <array>

using namespace clt::meta;

define_fn((static, constexpr), int, hello, (int, a), (int, b))
{
  return a + b;
}

#define PRINT_NAME(name) \
  std::cout << #name << ": " << name_of(reflect_info_of(name)) << '\n'
#define PRINT(name) std::cout << #name << ": " << (name) << '\n'

int main()
{
  define_using(u28, uint32_t);

  constexpr auto info_hello = reflect_info_of_nt(hello);
  to_tupled(info_hello)(std::tuple{10, 20});
  PRINT(name_of(reflect_info_of_nt(hello)));
  PRINT(to_string(reflect_info_of_nt(u28)));
  constexpr auto hello_args = clt::meta::arguments_of(info_hello);
  for_each(hello_args, [](auto&& a) noexcept {
        std::cout << clt::meta::name_of(reflect_info_of(reflect_type_of(a))) << ' '
                  << clt::meta::name_of(a) << '\n';
  });
}