// SC_METHOD + 静的感度 + ヘルパメソッド + 利用者定義の関数（ルールで追加）
#include <systemc>

extern "C" unsigned int parity(unsigned int x);   // プロジェクト独自の関数

SC_MODULE(Counter) {
  sc_core::sc_event tick;
  sc_core::sc_event wrapped;
  uint32_t count;
  uint32_t limit = 5;
  uint32_t odd;

  SC_CTOR(Counter) : count(0) {
    SC_METHOD(on_tick);
    sensitive << tick;
    dont_initialize();
    SC_THREAD(clock);
  }

  uint32_t next(uint32_t c) const {
    if (c + 1 >= limit) return 0;
    return c + 1;
  }

  void on_tick() {
    count = next(count);
    odd = parity(count);
    if (count == 0)
      wrapped.notify();
  }

  void clock() {
    while (true) {
      wait(10, sc_core::SC_NS);
      tick.notify();
    }
  }
};
