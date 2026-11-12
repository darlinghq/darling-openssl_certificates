# Copyright (C) 2026 Lubos Dolezel
#
# Checks the shipped trust store data against the release it was imported from
# (Apple security_certificates 55349.120.10) and the generated bundle's
# internal consistency.  Standard library only.

import base64
import hashlib
import pathlib
import plistlib
import re
import runpy
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = pathlib.Path(__file__).resolve().parents[1]


def der(path):
    text = path.read_text()
    body = re.search(r"-----BEGIN CERTIFICATE-----(.*?)-----END CERTIFICATE-----", text, re.S)
    return base64.b64decode("".join(body.group(1).split()))


class BundleContentsTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.output = tempfile.TemporaryDirectory()
        cls.addClassCleanup(cls.output.cleanup)
        script = ROOT / "scripts/generate-ca-bundle.py"
        with patch.object(sys, "argv", [str(script), cls.output.name]):
            runpy.run_path(str(script))
        cls.resources = pathlib.Path(cls.output.name) / "Certificates.bundle/Contents/Resources"
        cls.certs = {p.name: der(p) for p in (ROOT / "certs").glob("*.crt")}

    def test_every_certificate_is_indexed_once(self):
        index = (self.resources / "certsIndex.data").read_bytes()
        self.assertEqual(len(index), 24 * len(self.certs))

    def test_roots_removed_from_apple_list_are_absent(self):
        # Subject strings of roots Apple moved to certificates/removed
        # (distrusted or retired) between 55219.100.22 and 55349.120.10.
        for subject in [b"TrustCor RootCert CA-1", b"TrustCor RootCert CA-2", b"TrustCor ECA-1",
                        b"E-Tugra Certification Authority", b"CNNIC ROOT", b"StartCom Certification Authority",
                        b"Certinomis - Root CA", b"Certinomis - Autorit", b"VeriSign Universal Root",
                        b"GeoTrust Global CA", b"Baltimore CyberTrust Root", b"Hongkong Post Root CA 1"]:
            with self.subTest(subject=subject):
                self.assertFalse([n for n, d in self.certs.items() if subject in d],
                                 "%r is still shipped" % subject)

    def test_apple_private_policy_roots_are_withheld(self):
        # Apple restricts these to Apple-private policy OIDs; the consuming
        # trust code has no per-anchor policy constraints.
        self.assertFalse([n for n, d in self.certs.items() if b"Apple Platform" in d])

    def test_ev_roots_refer_to_shipped_certificates(self):
        sha1s = {hashlib.sha1(d).digest() for d in self.certs.values()}
        ev = plistlib.loads((self.resources / "EVRoots.plist").read_bytes())
        self.assertIn("2.23.140.1.1", ev)
        for oid, digests in ev.items():
            for digest in digests:
                with self.subTest(oid=oid):
                    self.assertIn(digest, sha1s)

    def test_block_lists_and_version(self):
        for name in ("Blocked.plist", "GrayListedKeys.plist"):
            self.assertIsInstance(plistlib.loads((self.resources / name).read_bytes()), list)
        version = plistlib.loads((self.resources / "AssetVersion.plist").read_bytes())
        self.assertGreaterEqual(version["VersionNumber"], 2026040100)


if __name__ == "__main__":
    unittest.main()
