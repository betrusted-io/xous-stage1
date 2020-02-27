# Xous Stage 1 Loader

This contains the stage1 for Xous.  This program is responsible for
parsing the initial boot arguments, setting up memory maps, and
preparing the kernel and its initial programs to run.

This program runs in **Machine** mode and has access to the entire system.  When it jumps to the kernel, the system will be in **Supervisor** mode with no way to return to **Machine** mode.

## Building

To build the stage-1 module, you will need a basic `riscv32i-unknown-none-elf` target for Rust.

1. Get Rust.  Go to https://rustup.rs/ and follow its instructions.
2. Install the proper toolchain: `rustup target add riscv32i-unknown-none-elf`
3. Build the stage-1 loader: `cargo build --release`
4. Get an executable binary: `riscv64-unknown-elf-gcc -O binary target/riscv32i-unknown-none-elf/xous-stage1 xous-stage1.bin`

## Using

This requires additional components in order to function:

1. A kernel to run, and optionally additional init processes
2. A kernel arguments structure to indicate memory regions
3. A stage-0 bootloader to set up the arguments

The stage-0 bootloader needs to load the kernel arguments structure into memory at some address, then set register `$a0` (also known as `$x10` or `R10` in RISC-V) to point there.  It then needs to jump to that address.

For example, in [Renode](https://github.com/renode/renode/), this is accomplished with the following commands:

```
    sysbus LoadELF @../stage1/target/riscv32i-unknown-none-elf/debug/xous-stage1
    sysbus LoadBinary @../tools/args.bin 0x40800000
    # Set $a0 to point at the args binary
    cpu SetRegisterUnsafe 10 0x40800000
    cpu PC 0x20500000
```

There is no additional setup required.

## Testing

_TBD_

## Contribution Guidelines

[![Contributor Covenant](https://img.shields.io/badge/Contributor%20Covenant-v2.0%20adopted-ff69b4.svg)](CODE_OF_CONDUCT.md)

Please see [CONTRIBUTING](CONTRIBUTING.md) for details on
how to make a contribution.

Please note that this project is released with a
[Contributor Code of Conduct](CODE_OF_CONDUCT.md).
By participating in this project you agree to abide its terms.

## License

Copyright © 2020

Licensed under the [Apache License 2.0](http://opensource.org/licenses/Apache-2.0) [LICENSE](LICENSE)
