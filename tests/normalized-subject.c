#include <CoreFoundation/CoreFoundation.h>
#include <Security/Security.h>
#include <stdio.h>
#include <stdlib.h>

/* Declared by the vendored Security trust/headers/SecCertificatePriv.h. */
extern CFDataRef SecCertificateCopyNormalizedSubjectSequence(SecCertificateRef);

int main(int argc, char **argv) {
    if (argc != 3) return 2;
    FILE *input = fopen(argv[1], "rb");
    if (!input || fseek(input, 0, SEEK_END)) return 3;
    long length = ftell(input);
    if (length <= 0 || length > 1024 * 1024 || fseek(input, 0, SEEK_SET)) return 3;
    unsigned char *bytes = malloc(length);
    if (!bytes || fread(bytes, 1, length, input) != (size_t)length) return 3;
    fclose(input);
    CFDataRef data = CFDataCreate(NULL, bytes, length);
    free(bytes);
    SecCertificateRef certificate = SecCertificateCreateWithData(NULL, data);
    CFRelease(data);
    if (!certificate) return 4;
    CFDataRef normalized = SecCertificateCopyNormalizedSubjectSequence(certificate);
    CFRelease(certificate);
    if (!normalized) return 5;
    FILE *output = fopen(argv[2], "wb");
    if (!output) return 6;
    size_t written = fwrite(CFDataGetBytePtr(normalized), 1, CFDataGetLength(normalized), output);
    int closed = fclose(output);
    int result = written == (size_t)CFDataGetLength(normalized) && !closed ? 0 : 6;
    CFRelease(normalized);
    return result;
}
