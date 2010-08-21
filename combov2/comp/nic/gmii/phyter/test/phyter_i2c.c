#include "phyter_i2c.h"

void write_bit(cs_device_t *dev, cs_space_t *phy, u_int32_t sel,
        u_int32_t data) {

    u_int32_t data_bit;

    data_bit = (data == 1) ? WR_DATA_BIT : 0;

    cs_space_write_4(dev, phy, 0x0, (0x04 | data_bit) << sel*8);
    sleep(1);
    cs_space_write_4(dev, phy, 0x0, (0x14 | data_bit) << sel*8);
    sleep(1);
    cs_space_write_4(dev, phy, 0x0, (0x04 | data_bit) << sel*8);
    sleep(1);
}

u_int32_t read_bit(cs_device_t *dev, cs_space_t *phy, u_int32_t sel) {

    u_int32_t data_bit;

    cs_space_write_4(dev, phy, 0x0, 0x24 << sel*8);
    sleep(1);
    cs_space_write_4(dev, phy, 0x0, 0x34 << sel*8);
    sleep(1);

    data_bit = cs_space_read_4(dev, phy, 0x0);

    cs_space_write_4(dev, phy, 0x0, 0x24 << sel*8);
    sleep(1);

    return ((data_bit >> sel*8) & RD_DATA_FLAG) >> 1;
}

bool bus_busy(cs_device_t *dev, cs_space_t *phy, u_int32_t sel) {

    u_int32_t bus;

    bus = cs_space_read_4(dev, phy, 0);

    /* bus is free when SCL & SDA = 1 */
    return (bus >> sel*8) & (RD_CLK_FLAG | RD_DATA_FLAG) != 0x3;
}

void start_cond(cs_device_t *dev, cs_space_t *phy, u_int32_t sel) {

    cs_space_write_4(dev, phy, 0x0, 0x54 << sel*8);
    sleep(1);
    cs_space_write_4(dev, phy, 0x0, 0x14 << sel*8);
    sleep(1);
    cs_space_write_4(dev, phy, 0x0, 0x04 << sel*8);
    sleep(1);
}

void stop_cond(cs_device_t *dev, cs_space_t *phy, u_int32_t sel) {

    cs_space_write_4(dev, phy, 0x0, 0x04 << sel*8);
    sleep(1);
    cs_space_write_4(dev, phy, 0x0, 0x14 << sel*8);
    sleep(1);
    cs_space_write_4(dev, phy, 0x0, 0x54 << sel*8);
    sleep(1);
    cs_space_write_4(dev, phy, 0x0, 0x7c << sel*8);
}

void send_addr(cs_device_t *dev, cs_space_t *phy, u_int32_t sel,
        u_int32_t addr, u_int32_t rw) {

    int i;

    /* write address bits (MSB first) */
    for (i=6; i >= 0; i--) {
        write_bit(dev, phy, sel, (addr >> i) & 0x1);
    }
    /* write r/w bit */
    write_bit(dev, phy, sel, rw & 0x1);
}

u_int32_t read_byte(cs_device_t *dev, cs_space_t *phy, u_int32_t sel) {

    int i;
    u_int32_t data = 0;

    for (i=0; i < 8; i++) {
        data = (data << 1) | read_bit(dev, phy, sel);
    }

    return data;
}

bool read_ack(cs_device_t *dev, cs_space_t *phy, u_int32_t sel) {

    /*
     * ACK : SDA = 0
     * !ACK: SDA = 1
     */
    return read_bit(dev, phy, sel) == 0x0;
}

void send_ack(cs_device_t *dev, cs_space_t *phy, u_int32_t sel, bool ack) {

    /*
     * ACK : SDA = 0
     * !ACK: SDA = 1
     */
    if (ack)
        write_bit(dev, phy, sel, 0x0);
    else
        write_bit(dev, phy, sel, 0x1);
}
