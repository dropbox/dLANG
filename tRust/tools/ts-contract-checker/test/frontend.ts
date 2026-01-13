/**
 * Test frontend with intentional contract violations
 */

interface User {
  id: number;
  email: string;
  age: number;
}

const API_BASE = "/api";

/**
 * VIOLATION: No validation before API call
 * Contract requires: email.len() > 0 && age >= 18
 */
async function createUser(email: string, age: number): Promise<User> {
  // No validation - violates preconditions
  const response = await fetch(`${API_BASE}/users`, {
    method: "POST",
    body: JSON.stringify({ email, age }),
  });
  return response.json();
}

/**
 * CORRECT: Validates precondition id > 0
 */
async function getUser(id: number): Promise<User | null> {
  if (id <= 0) {
    throw new Error("Invalid user ID");
  }
  const response = await fetch(`${API_BASE}/users/${id}`);
  return response.json();
}

export { createUser, getUser };
