// 制約違反の例: 条件分岐の中の wait と、ポインタ演算
#include <systemc>

SC_MODULE(Bad) {
  sc_core::sc_event ev;
  uint32_t x;
  uint32_t* p;

  SC_CTOR(Bad) {
    SC_THREAD(run);
  }

  void run() {
    while (true) {
      if (x > 0)
        wait(ev);
      x = *(p + 1);
    }
  }
};
