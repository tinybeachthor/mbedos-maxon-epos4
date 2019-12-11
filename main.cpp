#include "mbed.h"
#include <inttypes.h>

// Blinking rate in milliseconds
#define BLINKING_RATE_MS 500

Serial pc(SERIAL_TX, SERIAL_RX);

int main() {
  // Initialise the digital leds
  DigitalOut led_power(LED1);
  DigitalOut led_status(LED2);
  DigitalOut led_error(LED3);

  while (true) {
    led_power = !led_power;
    wait_us(BLINKING_RATE_MS * 1000);
  }
}
