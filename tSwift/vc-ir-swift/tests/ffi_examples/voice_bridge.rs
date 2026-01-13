// Example Rust FFI using swift_bridge syntax
// This demonstrates verification with the swift_bridge::bridge attribute

#[swift_bridge::bridge]
mod voice_ffi {
    #[requires(sample_rate == 16000 || sample_rate == 48000)]
    #[ensures(result >= 0)]
    extern "Rust" {
        fn start_stt(sample_rate: u32) -> i32;
    }

    extern "Rust" {
        #[requires(text.len() > 0)]
        fn queue_tts(text: String) -> u64;

        #[trusted]
        fn stop_session();
    }
}
