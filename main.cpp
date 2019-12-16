#include "mbed.h"
#include <inttypes.h>

#include "epos4.hpp"

#include "debug.hpp"

#define BLINKING_RATE_MS 500

int main() {
  DigitalOut led_power(LED1);

  pc.printf("Starting up...");

  PinName can_rx; // TODO
  PinName can_tx; // TODO

  epos4::init(can_rx, can_tx);
  pc.printf("Setup complete!");
  wait_us(1000 * 1000);

  pc.printf("Turning motorcontroller on");
  epos4::startPosMode();
  wait_us(1000 * 1000);
  pc.printf("Motorcontroller on");

  pc.printf("Turning motorcontroller off");
  epos4::stop();
  wait_us(1000 * 1000);
  pc.printf("Motorcontroller off");

  while (true) {
    led_power = !led_power;
    wait_us(BLINKING_RATE_MS * 1000);
  }
}
