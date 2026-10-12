#!/usr/bin/env bash
# Recreate the BerkeleyGW 4.0 real-flavor serial build used by BGW-M4-R1/M5.
#
#   bash bgw/toolchain/setup.sh [DEST]      # default DEST=$HOME/bgw-src
#   export BGW_TOOLCHAIN=DEST/mm/envs/bgw   # printed at the end
#
# User space only: no sudo, no global configuration. The compiler and
# libraries come from conda-linux-64.lock (exact URLs + md5), the source from
# the SHA-256-pinned archive (docs/BERKELEYGW_4.0_GPP.md). The build uses
# bgw/export/arch.mk with only its toolchain prefix replaced.
set -euo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
DEST="$(mkdir -p "${1:-$HOME/bgw-src}" && cd "${1:-$HOME/bgw-src}" && pwd)"
ARCHIVE_URL="https://app.box.com/shared/static/22edl07muvhfnd900tnctsjjftbtcqc4.gz"
ARCHIVE_SHA256="1a85b03b83b339056f65124bfa96832ca61152236d9bb1cb372e3040fc686a49"
MICROMAMBA_URL="https://micro.mamba.pm/api/micromamba/linux-64/2.9.0"
ARCHIVED_PREFIX="/tmp/mm/root/envs/bgw"

cd "$DEST"
if [ ! -x bin/micromamba ]; then
  curl -sSL "$MICROMAMBA_URL" | tar -xj bin/micromamba
fi
export MAMBA_ROOT_PREFIX="$DEST/mm"
if [ ! -x "$MAMBA_ROOT_PREFIX/envs/bgw/bin/x86_64-conda-linux-gnu-gfortran" ]; then
  bin/micromamba create -y -q -n bgw --file "$REPO/bgw/toolchain/conda-linux-64.lock"
fi
PREFIX="$MAMBA_ROOT_PREFIX/envs/bgw"

if [ ! -f bgw40.tar.gz ]; then
  curl -sSL -o bgw40.tar.gz "$ARCHIVE_URL"
fi
echo "$ARCHIVE_SHA256  bgw40.tar.gz" | sha256sum -c -

if [ ! -x pristine/BerkeleyGW-4.0/Sigma/sigma.real.x ]; then
  rm -rf pristine && mkdir pristine && tar -xzf bgw40.tar.gz -C pristine
  T=pristine/BerkeleyGW-4.0
  sed "s#$ARCHIVED_PREFIX#$PREFIX#g" "$REPO/bgw/export/arch.mk" > "$T/arch.mk"
  cp "$T/flavor_real.mk" "$T/flavor.mk"
  (export PATH="$PREFIX/bin:$PATH"; cd "$T" && make -j8 epsilon > ../build-eps.log 2>&1 \
     && make -j8 sigma > ../build-sig.log 2>&1)
fi
# the EPM mean-field generator (endpoint E0 and the convergence sweeps)
if [ ! -x pristine/BerkeleyGW-4.0/MeanField/EPM/epm2bgw.x ]; then
  (export PATH="$PREFIX/bin:$PATH"; cd pristine/BerkeleyGW-4.0 \
     && make -j8 -C MeanField/EPM > ../build-epm.log 2>&1)
fi
# kgrid.x (irreducible k lists for the convergence sweeps)
if [ ! -x pristine/BerkeleyGW-4.0/MeanField/ESPRESSO/kgrid.x ]; then
  (export PATH="$PREFIX/bin:$PATH"; cd pristine/BerkeleyGW-4.0 \
     && make -C MeanField/ESPRESSO kgrid.x > ../build-kgrid.log 2>&1)
fi
sha256sum pristine/BerkeleyGW-4.0/Epsilon/epsinv.f90 pristine/BerkeleyGW-4.0/Sigma/mtxel_cor.f90
echo "export BGW_TOOLCHAIN=$PREFIX"
echo "pristine tree: $DEST/pristine/BerkeleyGW-4.0"
