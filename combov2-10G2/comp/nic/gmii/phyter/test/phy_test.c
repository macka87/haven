#include "phyter_i2c.h"

#define READ_OP 0x1
#define WRITE_OP 0x0

int main(int argc, char *argv[]) {

	cs_device_t    *dev;
	cs_space_t     *fpga;
	char           *file = CS_PATH_DEV(0);

    u_int32_t sel = 1;  /* 1 -> communicate with phyter B */
    u_int32_t data = 0;
    long base_address = 0x128000; /* design base address in SFPRO testing design */

    if (cs_attach_noex(&dev, file) != 0)
        return 1;

    printf("Device attached.\n");

	if (cs_space_map(dev, &fpga, CS_SPACE_FPGA, CS_MAP_ALL, base_address, 0) != 0)
		return 2;

    printf("Address space mapped.\n");

    /* start transfer only when bus is free */
    if (!bus_busy(dev, fpga, sel)) {
        /* first, send start bit */
        start_cond(dev, fpga, sel);

        printf("Start bit sent.\n");

        /* send phyter address */
        send_addr(dev, fpga, sel, (0xac) >> 1, READ_OP);

        printf("Address sent.\n");

        /* and wait for phyter to ACK */
        if (read_ack(dev, fpga, sel)) {

            printf("received ACK.\n");

            /* receive data byte */
            data = (data << 8) | read_byte(dev, fpga, sel);

            printf("Byte received.\n");

            /* send ACK -> accept more data */
            send_ack(dev, fpga, sel, true);

            printf("ACK sent.\n");

            /* receive secodn byte - phyter registers are 16b long */
            data = (data << 8) | read_byte(dev, fpga, sel);

            printf("Byte received.\n");

            /* send !ACK -> won't accept more data */
            send_ack(dev, fpga, sel, false);

            printf("!ACK sent.\n");

            printf("received data: 0x%08X\n", (u_int32_t) data);
        } else {
            /* phyter did not ACKed */
            printf("received !ACK.\n");
        }

        /* end transfer */
        stop_cond(dev, fpga, sel);

        printf("Stop bit sent.\n");

    } else
        return 3;

    return 0;
}
