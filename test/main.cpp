#include <clt/reflect.h>
#include <iostream>
#include <array>

using namespace clt::meta;

define_enum_class(TesASd, uint8_t, A, (B, 10), C);

define_fn((static, constexpr), int, hello, (int, a), (int, b))
{
  return a + b;
}

#define PRINT_NAME(name) \
  std::cout << #name << ": " << identifier_of(reflect_info_of(name)) << '\n'
#define PRINT(name) std::cout << #name << ": " << (name) << '\n'

int main()
{
  define_var((static), uint32_t, Hello, 10);

  PRINT(*enum_to_string(reflect_info_of_nt(TesASd))(TesASd::A));

  constexpr auto info_hello = reflect_info_of_nt(hello);
  to_tupled(info_hello)(std::tuple{10, 20});
  PRINT(identifier_of(reflect_info_of_nt(hello)));
  PRINT(to_string(info_hello));
  PRINT(to_string(reflect_info_of_const(2)));
  constexpr auto hello_args = clt::meta::arguments_of(info_hello);
  for_each(hello_args, [](auto&& a) noexcept {
        std::cout << clt::meta::identifier_of(reflect_info_of(reflect_type_of(a))) << ' '
                  << clt::meta::identifier_of(a) << '\n';
  });
}