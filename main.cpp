#include "mbed.h"

#include "epos4.hpp"

#include "debug.hpp"

#define BLINKING_RATE_MS 500

int main() {
  DigitalOut led_power(LED1);

  pc.printf("Starting up...");

  PinName can_rx = PD_0;
  PinName can_tx = PD_1;

  Epos4 mc(can_rx, can_tx);
  pc.printf("Setup complete!");
  wait_us(1000 * 1000);

  pc.printf("Turning motorcontroller on");
  mc.startPosMode();
  wait_us(1000 * 1000);
  pc.printf("Motorcontroller on");

  pc.printf("Turning motorcontroller off");
  mc.stop();
  wait_us(1000 * 1000);
  pc.printf("Motorcontroller off");

  while (true) {
    led_power = !led_power;
    wait_us(BLINKING_RATE_MS * 1000);
  }
}
