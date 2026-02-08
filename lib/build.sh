set -e
wit-deps
cargo build --lib --target wasm32-unknown-unknown --release
wasm-tools component new ./target/wasm32-unknown-unknown/release/render.wasm -o ./target/nightboy-lib.wasm
