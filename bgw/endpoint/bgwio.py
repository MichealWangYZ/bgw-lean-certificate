"""Independent readers for the BerkeleyGW 4.0 real-flavour binary files.

Written from the writers' source, not from BerkeleyGW's readers:
  WFN / RHO    Common/wfn_rho_vxc_io_inc.f90 (header, gvectors, data)
  eps0mat/epsmat  header as in Epsilon/epsmat_merge.f90:239-250, per-q records
               Epsilon/epsinv.f90:790-809 and Common/write_matrix.f90:125-134
               (one record per column)
gfortran sequential unformatted: each record is framed by int32 byte counts.
"""
import pathlib

import numpy as np


class Records:
    def __init__(self, path):
        self.buf = pathlib.Path(path).read_bytes()
        self.pos = 0

    def next(self):
        n = int(np.frombuffer(self.buf, "<i4", 1, self.pos)[0])
        start = self.pos + 4
        tail = int(np.frombuffer(self.buf, "<i4", 1, start + n)[0])
        if tail != n:
            raise ValueError(f"corrupt record framing at byte {self.pos}")
        self.pos = start + n + 4
        return self.buf[start:start + n]

    def done(self):
        return self.pos == len(self.buf)


class Reader:
    """Sequential typed reads from one record."""

    def __init__(self, raw):
        self.raw, self.off = raw, 0

    def take(self, dtype, count=1):
        a = np.frombuffer(self.raw, dtype, count, self.off)
        self.off += a.nbytes
        return a

    def i(self, n=1):
        a = self.take("<i4", n)
        return int(a[0]) if n == 1 else a.astype(np.int64)

    def d(self, n=1):
        a = self.take("<f8", n)
        return float(a[0]) if n == 1 else a.copy()

    def s(self, n):
        v = self.raw[self.off:self.off + n].decode()
        self.off += n
        return v

    def end(self):
        if self.off != len(self.raw):
            raise ValueError(f"record has {len(self.raw) - self.off} unread bytes")


def _header(rec, kind):
    r = Reader(rec.next())
    title = r.s(32)
    r.s(32), r.s(32)
    r.end()
    if title.strip() != f"{kind}-Real":
        raise ValueError(f"expected {kind}-Real, read {title.strip()!r}")
    wfn = kind == "WFN"
    h = {}
    r = Reader(rec.next())
    h["nspin"], h["ng"], h["ntran"], h["cell_symmetry"], h["nat"] = r.i(5)
    h["ecutrho"] = r.d()
    if wfn:
        h["nk"], h["nbands"], h["ngkmax"] = r.i(3)
        h["ecutwfc"] = r.d()
    r.end()
    r = Reader(rec.next())
    h["FFTgrid"] = r.i(3)
    if wfn:
        h["kgrid"] = r.i(3)
        h["kshift"] = r.d(3)
    r.end()
    r = Reader(rec.next())
    h["celvol"], h["alat"] = r.d(), r.d()
    h["avec"] = r.d(9).reshape(3, 3)      # avec[ii][jj] = avec(jj, ii): row ii is vector ii
    h["adot"] = r.d(9).reshape(3, 3)
    r.end()
    r = Reader(rec.next())
    h["recvol"], h["blat"] = r.d(), r.d()
    h["bvec"] = r.d(9).reshape(3, 3)
    h["bdot"] = r.d(9).reshape(3, 3)
    r.end()
    r = Reader(rec.next())
    # mtrx(ii, jj, itran) written ii fastest -> Fortran order
    h["mtrx"] = r.i(9 * h["ntran"]).reshape(h["ntran"], 3, 3).transpose(0, 2, 1).copy()
    r.end()
    r = Reader(rec.next())
    h["tnp"] = r.d(3 * h["ntran"]).reshape(h["ntran"], 3)
    r.end()
    r = Reader(rec.next())
    nat = h["nat"]
    raw = np.frombuffer(r.raw, np.dtype([("apos", "<f8", 3), ("atyp", "<i4")]), nat)
    h["apos"], h["atyp"] = raw["apos"].copy(), raw["atyp"].astype(int)
    if wfn:
        nk, nb, ns = h["nk"], h["nbands"], h["nspin"]
        h["ngk"] = Reader(rec.next()).i(nk) if nk > 1 else np.array([Reader(rec.next()).i()])
        h["kw"] = Reader(rec.next()).d(nk) if nk > 1 else np.array([Reader(rec.next()).d()])
        h["kpt"] = Reader(rec.next()).d(3 * nk).reshape(nk, 3)
        h["ifmin"] = Reader(rec.next()).i(nk * ns) if nk * ns > 1 else np.array([0])
        h["ifmax"] = Reader(rec.next()).i(nk * ns) if nk * ns > 1 else np.array([0])
        h["energies"] = Reader(rec.next()).d(nb * nk * ns).reshape(ns, nk, nb)
        h["occupations"] = Reader(rec.next()).d(nb * nk * ns).reshape(ns, nk, nb)
    return h


def _gvectors(rec, ng):
    nrec = Reader(rec.next()).i()
    out = []
    for _ in range(nrec):
        n = Reader(rec.next()).i()
        out.append(Reader(rec.next()).i(3 * n).reshape(n, 3))
    g = np.concatenate(out)
    if len(g) != ng:
        raise ValueError("gvector count mismatch")
    return g


def _data(rec, ng, ns):
    nrec = Reader(rec.next()).i()
    if nrec != 1:
        raise ValueError("multi-record data not supported")
    n = Reader(rec.next()).i()
    if n != ng:
        raise ValueError("data length mismatch")
    return Reader(rec.next()).d(ng * ns).reshape(ns, ng)


def read_wfn(path):
    rec = Records(path)
    h = _header(rec, "WFN")
    h["gvec"] = _gvectors(rec, h["ng"])
    h["kg"], h["coef"] = [], []
    for ik in range(h["nk"]):
        ngk = int(h["ngk"][ik])
        h["kg"].append(_gvectors(rec, ngk))
        h["coef"].append(np.array([_data(rec, ngk, h["nspin"])[0]
                                   for _ in range(h["nbands"])]))
    if not rec.done():
        raise ValueError("trailing records in WFN")
    return h


def read_rho(path, kind="RHO"):
    """RHO (or, with kind="VXC", the VXC file: same layout)."""
    rec = Records(path)
    h = _header(rec, kind)
    h["gvec"] = _gvectors(rec, h["ng"])
    h["rho"] = _data(rec, h["ng"], h["nspin"])[0]
    if not rec.done():
        raise ValueError(f"trailing records in {kind}")
    return h


def read_eps(path):
    """Static real epsmat/eps0mat, layout as written by Epsilon and mirrored in
    Epsilon/epsmat_merge.f90:239-250 and epsascbin.f90:151-191: header, then per
    q the index maps, kinetic energies, q, and the nmtx x nmtx inverse
    dielectric matrix, one record per column."""
    rec = Records(path)
    h = {}
    r = Reader(rec.next())
    h["ajname"], h["adate"] = r.s(6), r.s(11)
    r = Reader(rec.next())
    (h["freq_dep"], h["nFreq"], h["subspace"], h["matrix_in_subspace_basis"],
     h["keep_full_eps_static"]) = r.i(5)
    if h["freq_dep"] != 0 or h["subspace"] != 0:
        raise ValueError("only static full-basis epsmat supported")
    h["qgrid"] = Reader(rec.next()).i(3)
    for _ in range(3):                          # frequency record, two blanks
        if rec.next():
            raise ValueError("expected an empty record")
    h["ecuts"] = Reader(rec.next()).d()
    r = Reader(rec.next())
    nq = r.i()
    h["qpts_header"] = r.d(3 * nq).reshape(nq, 3)
    r.end()
    r = Reader(rec.next())
    ng = h["ng"] = r.i()
    h["gvec"] = r.i(3 * ng).reshape(ng, 3)
    r.end()
    h["q"] = []
    while not rec.done():
        r = Reader(rec.next())
        ngq, nmtx = r.i(2)
        pairs = r.i(2 * ngq).reshape(ngq, 2)
        r.end()
        ekin = Reader(rec.next()).d(ngq)
        q0 = Reader(rec.next()).d(3)
        cols = [Reader(rec.next()).d(nmtx) for _ in range(nmtx)]
        h["q"].append({"nmtx": nmtx, "isrtx": pairs[:, 0], "isorti": pairs[:, 1],
                       "ekin": ekin, "q": q0,
                       "epsinv": np.array(cols).T})   # epsinv[row, col]
    if len(h["q"]) != nq:
        raise ValueError("q-block count differs from header")
    return h


def read_eps_ff(path):
    """Full-frequency real-flavour epsmat/eps0mat: the frequency record
    (dFreqGrid real, dFreqBrd complex; Epsilon/inread.f90:565-605), then per q
    the index maps, kinetic energies, q, and for every column jj and row ii one
    record of nfreq complex retarded eps^-1 values (Common/write_matrix.f90:
    363-368)."""
    rec = Records(path)
    h = {}
    r = Reader(rec.next())
    h["ajname"], h["adate"] = r.s(6), r.s(11)
    r = Reader(rec.next())
    (h["freq_dep"], h["nFreq"], h["subspace"], h["matrix_in_subspace_basis"],
     h["keep_full_eps_static"]) = r.i(5)
    if h["freq_dep"] != 2 or h["subspace"] != 0:
        raise ValueError("expected a full-frequency, full-basis epsmat")
    nf = h["nFreq"]
    h["qgrid"] = Reader(rec.next()).i(3)
    r = Reader(rec.next())
    h["freq_grid"] = r.d(nf)
    h["freq_brd"] = r.take("<c16", nf).copy()
    r.end()
    for _ in range(2):
        if rec.next():
            raise ValueError("expected an empty record")
    h["ecuts"] = Reader(rec.next()).d()
    r = Reader(rec.next())
    nq = r.i()
    h["qpts_header"] = r.d(3 * nq).reshape(nq, 3)
    r = Reader(rec.next())
    ng = h["ng"] = r.i()
    h["gvec"] = r.i(3 * ng).reshape(ng, 3)
    h["q"] = []
    while not rec.done():
        r = Reader(rec.next())
        ngq, nmtx = r.i(2)
        pairs = r.i(2 * ngq).reshape(ngq, 2)
        ekin = Reader(rec.next()).d(ngq)
        q0 = Reader(rec.next()).d(3)
        E = np.zeros((nf, nmtx, nmtx), complex)
        for jj in range(nmtx):
            for ii in range(nmtx):
                E[:, ii, jj] = Reader(rec.next()).take("<c16", nf)
        h["q"].append({"nmtx": nmtx, "isrtx": pairs[:, 0], "isorti": pairs[:, 1],
                       "ekin": ekin, "q": q0, "epsinv": E})
    if len(h["q"]) != nq:
        raise ValueError("q-block count differs from header")
    return h
