#!/usr/bin/env python3
#
# Copyright (C) 2026 Lubos Dolezel
#
# Refreshes certs/ and security-bundle-resources/ from a checkout of Apple's
# open-source security_certificates project at a release tag:
#
#   import-security-certificates.py <security_certificates checkout>
#
# certs/ receives the trusted roots (certificates/roots) as PEM files.  A root
# that is already present keeps its file name; new ones are named after their
# subject common name.  Roots that Apple restricts to Apple-private policy OIDs
# (the "system" section of certificates/constraints.json) are not copied: the
# trust code that consumes the generated bundle has no per-anchor policy
# constraints, so they would become unrestricted anchors.
#
# Requires the "cryptography" Python module (import time only; the build does not).

import json
import os
import re
import shutil
import sys
from cryptography import x509
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.x509.oid import NameOID

def fingerprint(cert):
  return cert.fingerprint(hashes.SHA256()).hex().upper()

def load_certificate(path):
  with open(path, "rb") as f:
    data = f.read()
  try:
    return x509.load_der_x509_certificate(data)
  except ValueError:
    return x509.load_pem_x509_certificate(data)

def sanitized_name(cert):
  for oid in (NameOID.COMMON_NAME, NameOID.ORGANIZATIONAL_UNIT_NAME, NameOID.ORGANIZATION_NAME):
    attrs = cert.subject.get_attributes_for_oid(oid)
    if attrs:
      return re.sub(r"[^A-Za-z0-9._ -]+", "_", attrs[0].value).strip(" .") or "root"
  return "root"

if len(sys.argv) != 2:
  sys.exit("usage: %s <security_certificates checkout>" % sys.argv[0])

apple = sys.argv[1]
repo = os.path.dirname(os.path.dirname(os.path.realpath(__file__)))
certs_dir = os.path.join(repo, "certs")
resources_dir = os.path.join(repo, "security-bundle-resources")

with open(os.path.join(apple, "certificates", "constraints.json")) as f:
  apple_private = set(json.load(f)["system"].keys())

roots = {}
roots_dir = os.path.join(apple, "certificates", "roots")
for name in sorted(os.listdir(roots_dir)):
  if not name.endswith(".cer"):
    continue
  cert = load_certificate(os.path.join(roots_dir, name))
  roots[fingerprint(cert)] = cert

existing = {}
for name in os.listdir(certs_dir):
  cert = load_certificate(os.path.join(certs_dir, name))
  existing[fingerprint(cert)] = name

kept = {h: c for h, c in roots.items() if h not in apple_private}
used = set()
final = {}
for h, cert in sorted(kept.items()):
  if h in existing:
    final[h] = existing[h]
    used.add(existing[h])
for h, cert in sorted(kept.items()):
  if h in final:
    continue
  base = sanitized_name(cert)
  name = base + ".crt"
  if name in used or name in existing.values():
    name = "%s-%s.crt" % (base, h[:8])
  used.add(name)
  final[h] = name

for name in os.listdir(certs_dir):
  os.remove(os.path.join(certs_dir, name))
for h, name in final.items():
  with open(os.path.join(certs_dir, name), "wb") as f:
    f.write(kept[h].public_bytes(serialization.Encoding.PEM))

shutil.copyfile(os.path.join(apple, "certificates", "EVRoots.json"),
                os.path.join(resources_dir, "EVRoots.json"))
shutil.copyfile(os.path.join(apple, "config", "AssetVersion.plist"),
                os.path.join(resources_dir, "AssetVersion.plist"))
print("%d roots in Apple's list, %d written, %d withheld" % (len(roots), len(final), len(roots) - len(kept)))
