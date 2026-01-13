/**
 * Cross-Language Wiring Test - Frontend
 *
 * This file demonstrates TypeScript code that may violate Rust contracts.
 * Run with: npx ts-contract-checker -c contracts.json frontend.ts
 *
 * EXPECTED WARNINGS:
 * 1. createUser: age not validated (could be < 18)
 * 2. deleteUser: is_admin not validated
 * 3. processPayment: card_number validation missing
 * 4. searchProducts: limit could be > 100
 */

// =============================================================================
// User API Calls
// =============================================================================

/**
 * Create a new user
 *
 * WARNING: This call doesn't validate age >= 18 before sending
 */
async function createUser(email: string, age: number): Promise<number> {
  // BUG: No validation that email.len() > 0
  // BUG: No validation that age >= 18
  const response = await fetch("/api/users", {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify({ email, age }),
  });

  const data = await response.json();
  return data.id;
}

/**
 * Get user by ID - CORRECT
 *
 * This call correctly validates user_id > 0
 */
async function getUser(userId: number): Promise<User | null> {
  // GOOD: Validates precondition
  if (userId <= 0) {
    throw new Error("Invalid user ID");
  }

  const response = await fetch(`/api/users/${userId}`, {
    method: "GET",
  });

  if (!response.ok) {
    return null;
  }

  return response.json();
}

/**
 * Delete a user
 *
 * WARNING: Missing is_admin validation
 */
async function deleteUser(userId: number): Promise<boolean> {
  // PARTIAL: Validates user_id > 0
  if (userId <= 0) {
    throw new Error("Invalid user ID");
  }

  // BUG: Not checking if caller is_admin before calling
  const response = await fetch(`/api/users/${userId}`, {
    method: "DELETE",
  });

  return response.ok;
}

// =============================================================================
// Product API Calls
// =============================================================================

/**
 * Add item to cart
 *
 * WARNING: quantity validation is weak
 */
async function addToCart(productId: number, quantity: number): Promise<number> {
  // PARTIAL: Validates product_id
  if (productId <= 0) {
    throw new Error("Invalid product ID");
  }

  // BUG: Should also check quantity >= 1, but doesn't
  const response = await fetch("/api/cart/add", {
    method: "POST",
    body: JSON.stringify({ productId, quantity }),
  });

  const data = await response.json();
  return data.total;
}

/**
 * Process payment
 *
 * WARNING: Card number validation is insufficient
 */
async function processPayment(
  amount: number,
  cardNumber: string
): Promise<boolean> {
  // PARTIAL: Validates amount > 0
  if (amount <= 0) {
    throw new Error("Amount must be positive");
  }

  // BUG: Card number should be validated as 16 digits
  // Current validation is too weak
  if (cardNumber.length < 10) {
    throw new Error("Invalid card number");
  }

  const response = await fetch("/api/payment", {
    method: "POST",
    body: JSON.stringify({ amount, cardNumber }),
  });

  return response.ok;
}

// =============================================================================
// Search API Calls
// =============================================================================

/**
 * Search products
 *
 * WARNING: limit validation allows values > 100
 */
async function searchProducts(
  query: string,
  limit: number = 50
): Promise<Product[]> {
  // PARTIAL: Validates query
  if (!query || query.length === 0) {
    throw new Error("Query must not be empty");
  }

  // BUG: Should also validate 1 <= limit <= 100
  // But this allows limit > 100 which violates contract
  if (limit < 1) {
    limit = 10;
  }

  const response = await fetch(`/api/products/search?q=${query}&limit=${limit}`);
  return response.json();
}

// =============================================================================
// Types
// =============================================================================

interface User {
  id: number;
  email: string;
  age: number;
}

interface Product {
  id: number;
  name: string;
  price: number;
}

// =============================================================================
// Usage Examples (with bugs)
// =============================================================================

async function main() {
  // Example 1: Create user without age validation
  // The backend requires age >= 18, but we don't check
  const userId = await createUser("test@example.com", 16); // BUG: age < 18

  // Example 2: Delete without admin check
  // The backend requires is_admin = true
  await deleteUser(userId); // BUG: caller might not be admin

  // Example 3: Search with excessive limit
  // The backend requires limit <= 100
  const products = await searchProducts("laptop", 500); // BUG: limit > 100

  // Example 4: Payment without proper card validation
  // The backend requires specific card number format
  await processPayment(100, "1234"); // BUG: invalid card format
}

// Note: In a real application, these would be caught by the ts-contract-checker
// and flagged as potential contract violations BEFORE runtime.
