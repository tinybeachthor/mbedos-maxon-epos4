#include "mbed.h"

#include "epos4.hpp"

#include "debug.hpp"

#define BLINKING_RATE_MS 500

int main() {
  DigitalOut led_power(LED1);
  DigitalOut led_status(LED2);
  led_power = true;
  led_status = true;

  pc.printf("Starting up...\n");

  PinName can_rx = PD_0;
  PinName can_tx = PD_1;

  Epos4 mc(can_rx, can_tx);
  pc.printf("Setup complete!\n");
  wait_us(1000 * 1000);

  led_status = false;

  pc.printf("Turning motorcontroller on\n");
  mc.startPosMode();
  wait_us(1000 * 1000);
  pc.printf("Motorcontroller on\n");

  pc.printf("Steering to position\n");
  mc.moveToAngle(2.5f);
  wait_us(1000 * 1000);
  pc.printf("Steering done\n");

  // pc.printf("Turning motorcontroller off\n");
  // mc.stop();
  // wait_us(1000 * 1000);
  // pc.printf("Motorcontroller off\n");

  //led_status = false;

  while (true) {
    led_power = !led_power;
    wait_us(BLINKING_RATE_MS * 1000);
  }
}
