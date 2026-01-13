//! Cross-Language Wiring Test - Backend
//!
//! This file demonstrates contracts that can be exported for TypeScript verification.
//! Compile with: rustc -Zverify -Zexport-contracts=contracts.json backend.rs
//!
//! @expect: VERIFIED

// =============================================================================
// User API Contracts
// =============================================================================

/// Create a new user
///
/// # Contract
/// - Email must not be empty
/// - Age must be >= 18 (adult)
/// - Returns a valid user ID
#[requires("email.len() > 0")]
#[requires("age >= 18")]
#[ensures("result > 0")]
pub fn create_user(email: &str, age: u32) -> u64 {
    // Simulated implementation
    42
}

/// Get user by ID
///
/// # Contract
/// - User ID must be positive
/// - Returns valid user data or None
#[requires("user_id > 0")]
pub fn get_user(user_id: u64) -> Option<User> {
    Some(User {
        id: user_id,
        email: String::from("test@example.com"),
        age: 25,
    })
}

/// Delete a user
///
/// # Contract
/// - User ID must be positive
/// - Caller must have admin privileges
#[requires("user_id > 0")]
#[requires("is_admin")]
#[ensures("result == true || result == false")]
pub fn delete_user(user_id: u64, is_admin: bool) -> bool {
    is_admin && user_id > 0
}

// =============================================================================
// Product API Contracts
// =============================================================================

/// Add item to cart
///
/// # Contract
/// - Product ID must be positive
/// - Quantity must be at least 1
/// - Returns new cart total
#[requires("product_id > 0")]
#[requires("quantity >= 1")]
#[ensures("result >= 0")]
pub fn add_to_cart(product_id: u64, quantity: u32) -> i32 {
    (quantity as i32) * 100 // Simulated price
}

/// Process payment
///
/// # Contract
/// - Amount must be positive
/// - Card number must be 16 digits (simplified check)
#[requires("amount > 0")]
#[requires("card_number >= 1000000000000000")]
#[requires("card_number <= 9999999999999999")]
#[ensures("result == true || result == false")]
pub fn process_payment(amount: u64, card_number: u64) -> bool {
    amount > 0 && card_number >= 1000000000000000
}

// =============================================================================
// Search API Contracts
// =============================================================================

/// Search products
///
/// # Contract
/// - Query must not be empty
/// - Limit must be between 1 and 100
#[requires("query.len() > 0")]
#[requires("limit >= 1")]
#[requires("limit <= 100")]
pub fn search_products(query: &str, limit: u32) -> Vec<Product> {
    vec![Product {
        id: 1,
        name: String::from("Test Product"),
        price: 999,
    }]
}

// =============================================================================
// Data Types
// =============================================================================

pub struct User {
    pub id: u64,
    pub email: String,
    pub age: u32,
}

pub struct Product {
    pub id: u64,
    pub name: String,
    pub price: u64,
}

// =============================================================================
// Main (for compilation test)
// =============================================================================

fn main() {
    // Test calls
    let user_id = create_user("test@example.com", 25);
    println!("Created user: {}", user_id);

    let user = get_user(user_id);
    println!("Got user: {:?}", user.is_some());

    let deleted = delete_user(user_id, true);
    println!("Deleted: {}", deleted);

    let cart_total = add_to_cart(1, 2);
    println!("Cart total: {}", cart_total);

    let paid = process_payment(100, 4111111111111111);
    println!("Payment: {}", paid);

    let products = search_products("test", 10);
    println!("Found {} products", products.len());
}
