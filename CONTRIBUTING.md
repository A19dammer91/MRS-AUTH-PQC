# Contributing to MRS-AUTH-PQC

Thank you for helping build a secure, post-quantum future! 🚀

## Pull Request Guidelines

Before submitting a Pull Request, please ensure your changes pass our local quality checks:

1. **Code Formatting:** Clean and format the Rust code:
   ```bash
   cargo fmt -- --check
   ```
2. **Linting:** Ensure there are no compiler or clippy warnings:
   ```bash
   cargo clippy --all-targets -- -D warnings
   ```
3. **Testing:** Run the full test suite (108+ tests):
   ```bash
   cargo test --all-features
   ```
4. **Benchmarks:** If you modified cryptographic or sampling paths, verify performance has not degraded:
   ```bash
   cargo bench --bench sampler_bench
   ```

## Formal Verification (EasyCrypt)
The core mathematical properties of this framework are formally verified using EasyCrypt (located in `proofs/`). If your changes affect the core Diophantine or sampling logic, please ensure the corresponding `.ec` files are updated and compile successfully.

## Security
Since this is an authentication and cryptographic framework, security is our top priority. Never commit secrets, and ensure memory-sensitive structures implement proper zeroization behavior.
