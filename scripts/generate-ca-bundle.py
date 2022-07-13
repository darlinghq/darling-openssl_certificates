#!/usr/bin/env python3

# NOTE(facekapow):
# this script is written in Python, but it's probably not very
# idiomatic Python; i'm used to writing Node.js scripts
# (but Darling already has Python scripts in its build, so it's best to use it)

from hashlib import sha1
from enum import IntEnum
from functools import reduce
from operator import add
from os import listdir, path, makedirs
from base64 import b64decode, b64encode
from argparse import ArgumentParser
from shutil import copyfile
import re

CRT_CERTIFICATE_HEADER = "-----BEGIN CERTIFICATE-----"
CRT_CERTIFICATE_FOOTER = "-----END CERTIFICATE-----"

def round_up_to_multiple(x, multiple):
  mod = x % multiple
  if mod == 0:
    return x
  return x + (multiple - mod)

def int_byte_count(x):
  return (x.bit_length() + 7) // 8

# courtesy of https://stackoverflow.com/a/30375198/6620880 (but modified slightly)
def int_to_bytes(x):
  return x.to_bytes(int_byte_count(x), "big", signed = False)

def int_from_bytes(xbytes):
  return int.from_bytes(xbytes, "big", signed = False)

# i *would* use an ASN.1 module for Python, except that that would add another dependency
# to Darling's build, which i prefer not to do
# (users would have to `pip install <whatever>`)
#
# so instead, i have to reimplement DER encoding/decoding
# (at least it's not that hard)

DER_IDENTIFIER_CLASS = 0b11000000
DER_IDENTIFIER_CONSTRUCTED = 0b00100000
DER_IDENTIFIER_TYPE = 0b00011111

DER_IDENTIFIER_CLASS_OFFSET = 6
DER_IDENTIFIER_CONSTRUCTED_OFFSET = 5
DER_IDENTIFIER_TYPE_OFFSET = 0

DER_IDENTIFIER_TYPE_LONG_FORM_INDICIATOR = 0b10000000
DER_IDENTIFIER_TYPE_LONG_FORM_BITS = 0b01111111

DER_IDENTIFIER_TYPE_LONG_FORM_BIT_COUNT = 7

DER_LENGTH_LONG_FORM_INDICATOR = 0b10000000
DER_LENGTH_INITIAL_BYTE_BITS = 0b01111111

EVROOT_VALID_ITEM_REGEX = r"^\s*([0-9.]+)(?:(?:\s*\"[^\"]+\")+)\s*$"
# this assumes that no filenames will contain '"'
EVROOT_FILE_REGEX = r"\"([^\"]+)\""

class DERClass(IntEnum):
  Universal = 0
  Application = 1
  ContextSpecific = 2
  Private = 3

class DERTag(IntEnum):
  EOC = 0
  Boolean = 1
  Integer = 2
  BitString = 3
  OctetString = 4
  Null = 5
  ObjectIdentifier = 6
  ObjectDescriptor = 7
  External = 8
  Real = 9
  Enumerated = 10
  EmbeddedPDV = 11
  UTF8String = 12
  RelativeOID = 13
  Time = 14
  Sequence = 16
  Set = 17
  NumericString = 18
  PrintableString = 19
  TeletexString = 20
  VideotexString = 21
  IA5String = 22
  UTCTime = 23
  GeneralizedTime = 24
  GraphicString = 25
  VisibleString = 26
  GeneralString = 27
  UniversalString = 28
  CharacterString = 29
  BMPString = 30
  Date = 31
  TimeOfDay = 32
  DateTime = 33
  Duration = 34
  OIDIRI = 35
  RelativeOIDIRI = 36

class DER:
  def __init__(self, tag, content, constructed = False, klass = DERClass.Universal):
    self.tag = tag
    self.constructed = constructed
    self.klass = klass
    self.content = content

  @property
  def content_length(self):
    return len(self.content)

  @property
  def length(self):
    total_length = 2

    if self.tag > 30:
      tmp = self.tag
      while tmp > 0:
        tmp >>= DER_IDENTIFIER_TYPE_LONG_FORM_BIT_COUNT
        total_length += 1

    if self.content_length > 127:
      total_length += int_byte_count(self.content_length)

    return total_length + self.content_length

  @staticmethod
  def decode(der_bytes):
    klass = (der_bytes[0] & DER_IDENTIFIER_CLASS) >> DER_IDENTIFIER_CLASS_OFFSET
    constructed = bool(der_bytes[0] & DER_IDENTIFIER_CONSTRUCTED)
    tag = (der_bytes[0] & DER_IDENTIFIER_TYPE) >> DER_IDENTIFIER_TYPE_OFFSET
    offset = 1

    # if it's the max value,
    # then it's a a long form tag
    if tag == DER_IDENTIFIER_TYPE:
      tag = 0
      while True:
        curr = der_bytes[offset]
        tag <<= DER_IDENTIFIER_TYPE_LONG_FORM_BIT_COUNT
        tag |= curr & DER_IDENTIFIER_TYPE_LONG_FORM_BITS
        offset += 1
        if not (curr & DER_IDENTIFIER_TYPE_LONG_FORM_INDICIATOR):
          break

    content_length = der_bytes[offset] & DER_LENGTH_INITIAL_BYTE_BITS
    if der_bytes[offset] & DER_LENGTH_LONG_FORM_INDICATOR:
      # long form
      length_byte_count = content_length
      content_length = int_from_bytes(der_bytes[(offset + 1):(offset + 1 + length_byte_count)])
      offset += length_byte_count
    offset += 1

    return DER(tag, der_bytes[offset:(offset + content_length)], constructed, klass)

  def encode(self):
    der_bytes = bytearray()
    first_byte = 0
    first_byte |= int(self.klass) << DER_IDENTIFIER_CLASS_OFFSET
    first_byte |= int(self.constructed) << DER_IDENTIFIER_CONSTRUCTED_OFFSET
    first_byte |= (DER_IDENTIFIER_TYPE if self.tag > 30 else self.tag) << DER_IDENTIFIER_TYPE_OFFSET
    der_bytes.append(first_byte)

    if self.tag > 30:
      tmp = self.tag
      while tmp > 0:
        byte = tmp & DER_IDENTIFIER_TYPE_LONG_FORM_BITS
        if (tmp >> DER_IDENTIFIER_TYPE_LONG_FORM_BIT_COUNT) > 0:
          byte |= DER_IDENTIFIER_TYPE_LONG_FORM_INDICIATOR
        tmp >>= DER_IDENTIFIER_TYPE_LONG_FORM_BIT_COUNT
        der_bytes.append(byte)

    if self.content_length > 127:
      # long form
      len_bytes = int_to_bytes(self.content_length)
      len_byte_count = len(len_bytes) & DER_LENGTH_INITIAL_BYTE_BITS
      len_byte_count |= DER_LENGTH_LONG_FORM_INDICATOR
      der_bytes.append(len_byte_count)
      der_bytes += len_bytes
    else:
      # short form
      der_bytes.append(self.content_length & DER_LENGTH_INITIAL_BYTE_BITS)

    der_bytes += self.content

    return bytes(der_bytes)

class X501AttributeTypeAndValue:
  def __init__(self, type, value):
    self.type = type
    self.value = value

class X501Name:
  def __init__(self, rdns):
    self.realtive_distinguished_names = rdns

  @staticmethod
  def decode(name_bytes):
    name_der = DER.decode(name_bytes)
    assert name_der.tag == DERTag.Sequence
    assert name_der.constructed

    name_idx = 0
    realtive_distinguished_names = []

    while name_idx < name_der.content_length:
      rdn_der = DER.decode(name_der.content[name_idx:])
      assert rdn_der.tag == DERTag.Set
      assert rdn_der.constructed
      assert rdn_der.length > 2 # need at least one element

      rdn = []

      rdn_idx = 0
      while rdn_idx < rdn_der.content_length:
        atv_der = DER.decode(rdn_der.content[rdn_idx:])
        assert atv_der.tag == DERTag.Sequence
        assert atv_der.constructed

        oid = DER.decode(atv_der.content)
        assert oid.tag == DERTag.ObjectIdentifier

        value_der = DER.decode(atv_der.content[oid.length:])
        assert (
          value_der.tag == DERTag.PrintableString or
          value_der.tag == DERTag.UTF8String or
          value_der.tag == DERTag.IA5String or
          value_der.tag == DERTag.TeletexString or
          value_der.tag == DERTag.BMPString or
          value_der.tag == DERTag.UniversalString
        )

        rdn.append(X501AttributeTypeAndValue(oid, value_der))

        rdn_idx += atv_der.length

      realtive_distinguished_names.append(rdn)

      name_idx += rdn_der.length

    return X501Name(realtive_distinguished_names)

  def encode(self):
    encoded_rdns = []
    for rdn in self.realtive_distinguished_names:
      encoded_atvs = []
      for atv in rdn:
        encoded_atvs.append(DER(DERTag.Sequence, atv.type.encode() + atv.value.encode(), constructed = True))
      atv_bytes = reduce(add, map(DER.encode, encoded_atvs))
      encoded_rdns.append(DER(DERTag.Set, atv_bytes, constructed = True))
    rdn_bytes = reduce(add, map(DER.encode, encoded_rdns))
    return DER(DERTag.Sequence, rdn_bytes, constructed = True).encode()

# this class only extracts the fields we need to generate the hash
# (i.e. the subject)
class PartialX509Certificate:
  def __init__(self, cert_bytes):
    signed_cert_der = DER.decode(cert_bytes)
    assert signed_cert_der.tag == DERTag.Sequence
    assert signed_cert_der.constructed

    cert_der = DER.decode(signed_cert_der.content)
    assert cert_der.tag == DERTag.Sequence
    assert cert_der.constructed

    cert_content_offset = 0

    # versions are optional
    version_der = DER.decode(cert_der.content[cert_content_offset:])
    if version_der.klass == DERClass.ContextSpecific and version_der.tag == 0 and version_der.constructed:
      cert_content_offset += version_der.length
    else:
      version_der = None

    serial_num_der = DER.decode(cert_der.content[cert_content_offset:])
    assert serial_num_der.tag == DERTag.Integer
    cert_content_offset += serial_num_der.length

    sig_oid_der = DER.decode(cert_der.content[cert_content_offset:])
    assert sig_oid_der.tag == DERTag.Sequence
    assert sig_oid_der.constructed
    cert_content_offset += sig_oid_der.length

    issuer_der = DER.decode(cert_der.content[cert_content_offset:])
    assert issuer_der.tag == DERTag.Sequence
    assert issuer_der.constructed
    cert_content_offset += issuer_der.length

    validity_der = DER.decode(cert_der.content[cert_content_offset:])
    assert validity_der.tag == DERTag.Sequence
    assert validity_der.constructed
    cert_content_offset += validity_der.length

    subject_der = DER.decode(cert_der.content[cert_content_offset:])
    assert subject_der.tag == DERTag.Sequence
    assert subject_der.constructed
    cert_content_offset += subject_der.length

    # decode the subject
    self.subject = X501Name.decode(subject_der.encode())

def generate_subject_hash(cert_bytes):
  cert = PartialX509Certificate(cert_bytes)

  for rdn in cert.subject.realtive_distinguished_names:
    for atv in rdn:
      atv.value.content = reduce(lambda a, b: a + b' ' + b, atv.value.content.upper().split())

  return sha1(DER.decode(cert.subject.encode()).content).digest()

def generate_certificate_hash(cert_bytes):
  return sha1(cert_bytes).digest()

def certificate_to_bytes(cert_path):
  lines = []
  with open(cert_path, "r") as cert_file:
    lines = cert_file.readlines()
  assert len(lines) > 2 # need at least header, body, and footer
  assert lines[0].strip() == CRT_CERTIFICATE_HEADER
  assert lines[-1].strip() == CRT_CERTIFICATE_FOOTER
  return b64decode(reduce(add, map(str.strip, lines[1:-1])))

arg_parser = ArgumentParser(description = "Generate the Security CA bundle for Darling")
arg_parser.add_argument("out_dir", metavar = "out_dir", type = str, nargs = 1)
args = arg_parser.parse_args()

source_root_dir = path.dirname(path.dirname(path.realpath(__file__)))
certs_dir = path.join(source_root_dir, "certs")
resources_dir = path.join(source_root_dir, "security-bundle-resources")
source_cert_paths = listdir(certs_dir)
cert_table = bytearray()
cert_index = bytearray()
bundle_dir = path.join(args.out_dir[0], "Certificates.bundle")
content_dir = path.join(bundle_dir, "Contents")
resoure_out_dir = path.join(content_dir, "Resources")

# create the structure
makedirs(resoure_out_dir, exist_ok = True)

# key = certificate filename
# value = list of OIDs for EV policies for that certificate
evroots_list = {}

# key = EV policy OID
# value = list of SHA1 digests of certificates with that policy
evroots = {}

with open(path.join(resources_dir, "evroot.config"), "r") as evroot_cfg:
  contents = evroot_cfg.readlines()

  for line in contents:
    stripped = line.strip()

    if len(stripped) == 0 or stripped.startswith('#'):
      continue

    match = re.search(EVROOT_VALID_ITEM_REGEX, stripped)

    if match == None:
      continue

    oid = match.group(1)
    filenames = re.findall(EVROOT_FILE_REGEX, stripped)

    for filename in filenames:
      actual_filename = filename.replace(".cer", ".crt").replace(".der", ".crt")
      f_list = evroots_list.setdefault(actual_filename, [])
      if oid not in f_list:
        f_list.append(oid)
      if "2.23.140.1.1" not in f_list:
        f_list.append("2.23.140.1.1") # add the default EV policy OID

# add the certificate to the table
#
# also check if it's present in evroot.config
# if it is, then add its hash to EVRoots.plist
for source_cert_name in source_cert_paths:
  source_cert_bytes = certificate_to_bytes(path.join(certs_dir, source_cert_name))

  subject_hash = generate_subject_hash(source_cert_bytes)

  padded_cert_bytes = bytearray(source_cert_bytes)
  target_padded_len = round_up_to_multiple(len(padded_cert_bytes), 8)
  # align on 8 byte boundary by padding it with 0xff
  for i in range(len(padded_cert_bytes), target_padded_len):
    padded_cert_bytes.append(0xff)
  assert len(padded_cert_bytes) % 8 == 0

  cert_index += subject_hash
  cert_index += len(cert_table).to_bytes(4, "little", signed = False)

  cert_table += (len(padded_cert_bytes) + 8).to_bytes(4, "little", signed = False)
  cert_table += len(source_cert_bytes).to_bytes(4, "little", signed = False)
  cert_table += padded_cert_bytes

  if source_cert_name in evroots_list:
    cert_hash = generate_certificate_hash(source_cert_bytes)
    for oid in evroots_list[source_cert_name]:
      evroots.setdefault(oid, []).append(cert_hash)

with open(path.join(resoure_out_dir, "certsIndex.data"), "wb") as cert_index_file:
  cert_index_file.write(cert_index)

with open(path.join(resoure_out_dir, "certsTable.data"), "wb") as cert_table_file:
  cert_table_file.write(cert_table)

with open(path.join(resoure_out_dir, "EVRoots.plist"), "wb") as evroots_file:
  evroots_file.write(b"<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n")
  evroots_file.write(b"<!DOCTYPE plist PUBLIC \"-//Apple//DTD PLIST 1.0//EN\" \"http://www.apple.com/DTDs/PropertyList-1.0.dtd\">\n")
  evroots_file.write(b"<plist version=\"1.0\">\n")
  evroots_file.write(b"<dict>\n")

  for oid in evroots:
    evroots_file.write(b"<key>" + oid.encode('utf-8') + b"</key>\n")
    evroots_file.write(b"<array>\n")
    for h in evroots[oid]:
      evroots_file.write(b"<data>" + b64encode(h) + b"</data>\n")
    evroots_file.write(b"</array>\n")

  evroots_file.write(b"</dict>\n")
  evroots_file.write(b"</plist>\n")

for i in ["Allowed.plist", "AssetVersion.plist", "Blocked.plist", "GrayListedKeys.plist", "AppleESCertificates.plist"]:
  copyfile(path.join(resources_dir, i), path.join(resoure_out_dir, i))

for i in ["Info.plist", "version.plist"]:
  copyfile(path.join(resources_dir, i), path.join(content_dir, i))
