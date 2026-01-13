/**
 * Frontend TypeScript code with intentional contract violations
 *
 * This file demonstrates cross-language contract checking.
 * It contains several intentional violations that should be detected
 * by the ts-contract-checker tool.
 */

interface User {
  id: number;
  email: string;
  age: number;
  created_at: number;
}

interface CreateUserRequest {
  email: string;
  age: number;
}

interface ApiError {
  type: "InvalidEmail" | "UnderageUser" | "InternalError";
  message: string;
}

const API_BASE = "/api";

/**
 * Create a new user - VIOLATION: No age validation before calling
 *
 * Contract violation: The backend requires age >= 18, but this function
 * does not validate age before making the API call.
 */
async function createUser(email: string, age: number): Promise<User> {
  // VIOLATION: No validation that age >= 18
  // VIOLATION: No validation that email.len() > 0

  const response = await fetch(`${API_BASE}/users`, {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify({ email, age }),
  });

  if (!response.ok) {
    throw new Error("Failed to create user");
  }

  return response.json();
}

/**
 * Get user by ID - CORRECT implementation
 *
 * This function correctly validates the precondition before calling.
 */
async function getUser(id: number): Promise<User | null> {
  // Correctly validates precondition: id > 0
  if (id <= 0) {
    throw new Error("Invalid user ID");
  }

  const response = await fetch(`${API_BASE}/users/${id}`, {
    method: "GET",
  });

  if (response.status === 404) {
    return null;
  }

  if (!response.ok) {
    throw new Error("Failed to get user");
  }

  return response.json();
}

/**
 * Delete user - VIOLATION: Wrong HTTP method
 *
 * Contract violation: The backend expects DELETE, but this uses POST.
 */
async function deleteUser(id: number): Promise<void> {
  // Correctly validates precondition
  if (id <= 0) {
    throw new Error("Invalid user ID");
  }

  // VIOLATION: Wrong HTTP method - should be DELETE, not POST
  const response = await fetch(`${API_BASE}/users/${id}`, {
    method: "POST", // Should be DELETE
  });

  if (!response.ok) {
    throw new Error("Failed to delete user");
  }
}

/**
 * User registration form handler - VIOLATION: Missing precondition check
 *
 * This handler does not validate age before calling createUser,
 * which violates the backend's age >= 18 precondition.
 */
async function handleRegistration(formData: CreateUserRequest): Promise<User> {
  // VIOLATION: Should check age >= 18 before calling API
  // This could send underage users to the backend

  if (!formData.email) {
    throw new Error("Email is required");
  }

  // No age validation!
  return createUser(formData.email, formData.age);
}

/**
 * Batch create users - VIOLATION: No validation loop
 *
 * Creates multiple users without validating each one's preconditions.
 */
async function batchCreateUsers(
  users: CreateUserRequest[]
): Promise<User[]> {
  // VIOLATION: No validation of individual user preconditions
  const results: User[] = [];

  for (const user of users) {
    // Should validate: user.email.length > 0 && user.age >= 18
    const created = await createUser(user.email, user.age);
    results.push(created);
  }

  return results;
}

/**
 * Safe user creation - CORRECT implementation
 *
 * This function correctly validates all preconditions before calling.
 */
async function safeCreateUser(
  email: string,
  age: number
): Promise<User | ApiError> {
  // Correctly validates all preconditions
  if (email.length === 0) {
    return { type: "InvalidEmail", message: "Email must not be empty" };
  }

  if (age < 18) {
    return { type: "UnderageUser", message: "User must be at least 18" };
  }

  return createUser(email, age);
}

// Export for testing
export {
  createUser,
  getUser,
  deleteUser,
  handleRegistration,
  batchCreateUsers,
  safeCreateUser,
};
