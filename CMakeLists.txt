project(OpenSSL-Certificates)

cmake_minimum_required(VERSION 2.4.0)

if(COMMAND cmake_policy)
	cmake_policy(SET CMP0003 NEW)
	cmake_policy(SET CMP0005 NEW)
endif(COMMAND cmake_policy)


find_library(OpenSSL REQUIRED)

set(HASH_DIRECTORY "${CMAKE_BINARY_DIR}/certs")
file(MAKE_DIRECTORY "${HASH_DIRECTORY}")
file(GLOB certificates "${CMAKE_CURRENT_SOURCE_DIR}/certs/*.crt")

macro(hash_certificate cert hash)
	execute_process(
		COMMAND openssl x509 -noout -hash -in ${cert}
		OUTPUT_VARIABLE ${hash}
		OUTPUT_STRIP_TRAILING_WHITESPACE
	)
endmacro(hash_certificate)

foreach(certificate ${certificates})
	get_filename_component(certificate_name ${certificate} NAME)
	hash_certificate(${certificate} hash)

	set(ext 0)
	if(IS_SYMLINK "${HASH_DIRECTORY}/${hash}.${ext}")
		set(ext 1)
	endif(IS_SYMLINK "${HASH_DIRECTORY}/${hash}.${ext}")

	execute_process(
		COMMAND ${CMAKE_COMMAND} -E create_symlink "${certificate_name}" "${hash}.${ext}"
		WORKING_DIRECTORY "${HASH_DIRECTORY}"
	)

	install(FILES ${certificate} "${HASH_DIRECTORY}/${hash}.${ext}"
		DESTINATION libexec/darling/System/Library/OpenSSL/certs
	)
endforeach(certificate)
