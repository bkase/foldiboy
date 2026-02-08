set -e
(
  cd "$(dirname ../../lib/build.sh)" && ./$(basename ../../lib/build.sh)
)

# Detect WSL by checking whether the `wslinfo` command exists and reports a version
# WSL needs to run X11 for webGPU to run properly (not Wayland)
if command -v wslinfo >/dev/null 2>&1 && wslinfo --version >/dev/null 2>&1; then
  WAYLAND_DISPLAY="" cargo run --release
else
  cargo run --release
fi