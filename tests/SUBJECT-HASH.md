# Security anchor lookup hashes

Run `python3 -m unittest discover -s tests -v` from this repository. The original
generator fails the non-PrintableString and generated-index checks; the corrected
generator passes. The end-to-end check finds the bundled Comodo AAA root under
the hash returned by the authored Security normalization control.

Specification: published Security `OSX/sec/Security/SecCertificate.c`,
`createNormalizedX501Name` (rung 1). It folds ASCII case and space/tab runs only
for PrintableString; it preserves the other string encodings. Security's
`trust/trustd/SecCertificateSource.c:subject_to_anchors` hashes the normalized
name content. No Apple-install binaries or guest internals were inspected.

Compile `normalized-subject.c` as a Darwin Mach-O against the configured SDK,
CoreFoundation, Security and libSystem. Run it in a private prefix with a DER
certificate input and an output path. It writes the normalized subject SEQUENCE
returned by the vendored `SecCertificateCopyNormalizedSubjectSequence` API
(declared in `trust/headers/SecCertificatePriv.h`, rungs 2/4). Remove the outer
SEQUENCE tag/length and SHA1 the content to compare with its generated index key.
All 159 bundled public roots matched this control after the fix on ARM64 Asahi.

An independent authored SecTrust test of a public HTTPS peer chain fails to find
the already-bundled root through the original index, while supplying that same
root explicitly validates the chain. Regenerating the normal index should repair
default anchor lookup; it does not add trust anchors or waive certificate checks.
