/*
 * phyter_i2c component address space:
 *
 * A: bit | desc      B: bit | desc      C: bit | desc      D: bit | desc
 *    --------------     --------------     --------------     --------------
 *      0 | RD_CLK         8 | RD_CLK        16 | RD_CLK        24 | RD_CLK
 *      1 | RD_DATA        9 | RD_DATA       17 | RD_DATA       25 | RD_DATA
 *      2 | WRITE         10 | WRITE         18 | WRITE         26 | WRITE
 *      3 | WR_CLK_Z      11 | WR_CLK_Z      19 | WR_CLK_Z      27 | WR_CLK_Z
 *      4 | WR_CLK        12 | WR_CLK        20 | WR_CLK        28 | WR_CLK
 *      5 | WR_DATA_Z     13 | WR_DATA_Z     21 | WR_DATA_Z     29 | WR_DATA_Z
 *      6 | WR_DATA       14 | WR_DATA       22 | WR_DATA       30 | WR_DATA
 *
 */

#define RD_CLK_FLAG 1
#define RD_DATA_FLAG 2

#define WRITE_BIT 4
#define WR_CLK_Z_BIT 8
#define WR_CLK_BIT 16
#define WR_DATA_Z_BIT 32
#define WR_DATA_BIT 64

#include <compat.h>
#include <combosix.h>

#include <stdio.h>
#include <unistd.h>
#include <stdbool.h>

bool bus_busy(cs_device_t *dev, cs_space_t *phy, u_int32_t sel);

void start_cond(cs_device_t *dev, cs_space_t *phy, u_int32_t sel);

void stop_cond(cs_device_t *dev, cs_space_t *phy, u_int32_t sel);

void send_addr(cs_device_t *dev, cs_space_t *phy, u_int32_t sel,
        u_int32_t addr, u_int32_t rw);

void write_byte(cs_device_t *dev, cs_space_t *phy, u_int32_t sel,
        u_int32_t data);

u_int32_t read_byte(cs_device_t *dev, cs_space_t *phy, u_int32_t sel);

bool read_ack(cs_device_t *dev, cs_space_t *phy, u_int32_t sel);

void send_ack(cs_device_t *dev, cs_space_t *phy, u_int32_t sel, bool ack);
