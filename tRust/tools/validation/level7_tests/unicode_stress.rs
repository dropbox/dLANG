// Unicode stress test
fn main() {
    // Unicode identifiers
    let α = 1;
    let β = 2;
    let γ = α + β;

    // Unicode strings
    let emoji = "Hello 🌍🦀 World";
    let chinese = "你好世界";
    let arabic = "مرحبا بالعالم";
    let math = "∀x∈ℝ: x²≥0";

    // Unicode in comments
    // This is a comment with émojis: 🎉✨🚀

    // Combining characters
    let cafe = "café";
    let angstrom = "Å";

    assert_eq!(γ, 3);
    println!("Unicode stress test passed: {}", emoji);
}
