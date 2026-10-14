# Verus exercises

## Setup

1. Download the latest release for your platform from
   https://github.com/verus-lang/verus/releases and unzip it
   (tested with `0.2026.10.04`).
2. Run `./verus --version` in the unzipped folder. It prints the Rust toolchain it
   needs. Install it with `rustup install <toolchain>` (get rustup at https://rustup.rs).
   On macOS you may first need `xattr -d com.apple.quarantine -r <unzipped folder>`.
3. Put that folder on your `PATH`.
4. Install the `verus-analyzer` VS Code extension, and disable Rust analyzer. 

Check a file:

```sh
verus ex1_fib.rs
```

Compile and run it once it verifies:

```sh
verus ex1_fib.rs --compile && ./ex1_fib
```
