// Swift imports for the voice_bridge.rs Rust FFI

/// Import start_stt with matching constraints
@_ffi_import("start_stt")
@_ffi_requires("sample_rate == 16000 || sample_rate == 48000")
@_ffi_ensures("result >= 0")
func startSTT(_ sample_rate: UInt32) -> Int32

/// Import queue_tts with stronger precondition (OK - implies text.len() > 0)
@_ffi_import("queue_tts")
@_ffi_requires("text.count >= 2")
func queueTTS(_ text: String) -> UInt64

/// Import trusted function
@_ffi_import("stop_session")
@_ffi_trusted
func stopSession()
