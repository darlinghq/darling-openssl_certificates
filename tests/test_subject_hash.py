import hashlib
import pathlib
import runpy
import sys
import tempfile
import unittest
from unittest.mock import patch


class SubjectHashTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = pathlib.Path(__file__).resolve().parents[1]
        cls.output = tempfile.TemporaryDirectory()
        cls.addClassCleanup(cls.output.cleanup)
        script = cls.root / "scripts/generate-ca-bundle.py"
        with patch.object(sys, "argv", [str(script), cls.output.name]):
            cls.generator = runpy.run_path(str(script))

    def name(self, tag, value):
        g = self.generator
        attribute = g["X501AttributeTypeAndValue"](
            g["DER"](g["DERTag"].ObjectIdentifier, b"\x55\x04\x03"),
            g["DER"](tag, value),
        )
        return g["X501Name"]([[attribute]]).encode()

    def subject_hash(self, name):
        # The partial parser reads only the TBS fields through subject. These
        # synthetic fields exercise name normalization, not certificate validity.
        g = self.generator
        der, tags = g["DER"], g["DERTag"]
        empty = der(tags.Sequence, b"", constructed=True).encode()
        serial = der(tags.Integer, b"\x01").encode()
        tbs = der(tags.Sequence, serial + empty * 3 + name, constructed=True)
        certificate = der(tags.Sequence, tbs.encode(), constructed=True).encode()
        return g["generate_subject_hash"](certificate)

    def check_normalization(self, tag, value, expected):
        encoded = self.name(tag, expected)
        expected_hash = hashlib.sha1(self.generator["DER"].decode(encoded).content).digest()
        self.assertEqual(self.subject_hash(self.name(tag, value)), expected_hash)

    def test_printable_case_and_horizontal_whitespace(self):
        self.check_normalization(19, b" \tAlice\t  Smith  ", b"ALICE SMITH")

    def test_utf8_preserves_case_spacing_and_non_ascii(self):
        value = "  Al\u00efce  Smith\t".encode("utf-8")
        self.check_normalization(12, value, value)

    def test_other_string_types_are_unchanged(self):
        for tag, value in [(22, b"Alice  Smith"), (20, b"Alice  Smith"),
                           (30, "Alice  Smith".encode("utf-16-be")),
                           (28, "Alice  Smith".encode("utf-32-be"))]:
            with self.subTest(tag=tag):
                self.check_normalization(tag, value, value)

    def test_generated_index_matches_security_normalized_root(self):
        # Authored SecCertificateCopyNormalizedSubjectSequence control over this
        # bundled public root, hashed without its outer SEQUENCE tag/length.
        expected = bytes.fromhex("eead83e6edb095758eff8af2aaf637ce2f5eef40")
        resources = pathlib.Path(self.output.name) / "Certificates.bundle/Contents/Resources"
        index = (resources / "certsIndex.data").read_bytes()
        table = (resources / "certsTable.data").read_bytes()
        certificate = self.generator["certificate_to_bytes"](
            self.root / "certs/Comodo_AAA_Certificate_Services.crt"
        )
        matches = []
        for position in range(0, len(index), 24):
            if index[position:position + 20] == expected:
                offset = int.from_bytes(index[position + 20:position + 24], "little")
                length = int.from_bytes(table[offset + 4:offset + 8], "little")
                matches.append(table[offset + 8:offset + 8 + length])
        self.assertTrue(certificate in matches, "bundled root is missing under its Security lookup hash")


if __name__ == "__main__":
    unittest.main()
