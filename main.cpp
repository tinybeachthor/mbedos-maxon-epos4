#include "mbed.h"
#include <inttypes.h>

#include "epos4.hpp"

#include "debug.hpp"

#define BLINKING_RATE_MS 500

int main() {
  DigitalOut led_power(LED1);

  pc.printf("Starting up...")

  PinName can_rx; // TODO
  PinName can_tx; // TODO

  epos4::init(can_rx, can_tx);
  pc.printf("Setup complete!")
  wait(1);
  pc.printf("EPOS4 state : %d", epos4::getState());

  pc.printf("Turning motorcontroller on")
  epos4::start();
  wait(1);
  pc.printf("EPOS4 state : %d", epos4::getState());

  pc.printf("Turning motorcontroller off")
  epos4::stop();
  wait(1);
  pc.printf("EPOS4 state : %d", epos4::getState());

  while (true) {
    led_power = !led_power;
    wait_ms(BLINKING_RATE_MS);
  }
}
