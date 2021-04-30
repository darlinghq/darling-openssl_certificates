project(OpenSSL-Certificates)

cmake_minimum_required(VERSION 3.10)

if(COMMAND cmake_policy)
	cmake_policy(SET CMP0003 NEW)
	cmake_policy(SET CMP0005 NEW)
endif(COMMAND cmake_policy)

find_package(PkgConfig REQUIRED)
pkg_search_module(OPENSSL REQUIRED openssl)

set(HASH_DIRECTORY "${CMAKE_BINARY_DIR}/certs")
file(MAKE_DIRECTORY "${HASH_DIRECTORY}")
file(GLOB certificates "${CMAKE_CURRENT_SOURCE_DIR}/certs/*.crt")

macro(hash_certificate cert hash)
	execute_process(
		COMMAND openssl x509 -noout -subject_hash_old -in ${cert}
		OUTPUT_VARIABLE ${hash}
		OUTPUT_STRIP_TRAILING_WHITESPACE
	)
endmacro(hash_certificate)

set(all_hashes "")
foreach(certificate ${certificates})
	get_filename_component(certificate_name ${certificate} NAME)
	hash_certificate(${certificate} hash)

	set(ext 0)

	while (TRUE)
		list(FIND all_hashes "${hash}.${ext}" hash_exists)
		if (NOT hash_exists EQUAL -1)
			math (EXPR ext "${ext} + 1")
		else (NOT hash_exists EQUAL -1)
			break()
		endif (NOT hash_exists EQUAL -1)
	endwhile (TRUE)
	list(APPEND all_hashes "${hash}.${ext}")

	execute_process(
		COMMAND ${CMAKE_COMMAND} -E create_symlink "${certificate_name}" "${hash}.${ext}"
		WORKING_DIRECTORY "${HASH_DIRECTORY}"
	)

	install(FILES ${certificate} "${HASH_DIRECTORY}/${hash}.${ext}"
		DESTINATION libexec/darling/System/Library/OpenSSL/certs
	)
endforeach(certificate)

# build and install Security's `Certificates.bundle`
add_custom_command(
	OUTPUT "${HASH_DIRECTORY}/Certificates.bundle"
	COMMAND "${CMAKE_CURRENT_SOURCE_DIR}/scripts/generate-ca-bundle.py" "${HASH_DIRECTORY}"
)
add_custom_target(build-security-certificates ALL DEPENDS "${HASH_DIRECTORY}/Certificates.bundle")
install(DIRECTORY "${HASH_DIRECTORY}/Certificates.bundle"
	DESTINATION libexec/darling/System/Library/Security
)
