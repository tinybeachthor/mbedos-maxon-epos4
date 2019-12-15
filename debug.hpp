#pragma once

#include "mbed.h"

Serial pc(SERIAL_TX, SERIAL_RX);

DigitalOut led_status(LED2);
DigitalOut led_error(LED3);
