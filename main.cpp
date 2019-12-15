#include "mbed.h"
#include <inttypes.h>

#include "debug.hpp"

#define BLINKING_RATE_MS 500

int main() {
  DigitalOut led_power(LED1);

  pc.printf("Starting up...")

  rtospp::Process loom_rx_can(&can::loom::loom_receive_main, "loom can rx process");
  rtospp::Process loom_tx_can(&can::loom::loom_transmit_main, "loom can tx process");

  pc.printf("Setup complete!")

  while (true) {
    led_power = !led_power;
    wait_ms(BLINKING_RATE_MS);
  }
}
