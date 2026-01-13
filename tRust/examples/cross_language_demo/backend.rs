//! Backend API with verified contracts
//!
//! This example demonstrates cross-language contract verification.
//! The contracts defined here are exported to JSON and verified against
//! TypeScript frontend code by the ts-contract-checker.

/// User creation request
pub struct CreateUserRequest {
    pub email: String,
    pub age: u32,
}

/// User response
pub struct User {
    pub id: u64,
    pub email: String,
    pub age: u32,
    pub created_at: u64,
}

/// API error response
pub enum ApiError {
    InvalidEmail,
    UnderageUser,
    InternalError,
}

/// Create a new user
///
/// # API Endpoint
/// POST /api/users
///
/// # Contracts
/// - requires: email.len() > 0 (email must not be empty)
/// - requires: age >= 18 (user must be adult)
/// - ensures: result.id > 0 (returned user has valid ID)
/// - ensures: result.age == age (age is preserved)
#[trust::requires("email.len() > 0", label = "email must not be empty")]
#[trust::requires("age >= 18", label = "user must be adult")]
#[trust::ensures("result.id > 0")]
#[trust::ensures("result.age == age")]
#[trust::api(path = "/api/users", method = "POST")]
pub fn create_user(email: String, age: u32) -> Result<User, ApiError> {
    if email.is_empty() {
        return Err(ApiError::InvalidEmail);
    }
    if age < 18 {
        return Err(ApiError::UnderageUser);
    }

    // In a real implementation, this would insert into a database
    Ok(User {
        id: 1, // Would be auto-generated
        email,
        age,
        created_at: 1704307200, // Would be current timestamp
    })
}

/// Get user by ID
///
/// # API Endpoint
/// GET /api/users/{id}
///
/// # Contracts
/// - requires: id > 0 (valid user ID)
/// - ensures: result.is_some() implies result.unwrap().id == id
#[trust::requires("id > 0", label = "valid user ID")]
#[trust::ensures("result.is_some() ==> result.unwrap().id == id")]
#[trust::api(path = "/api/users/{id}", method = "GET")]
#[trust::pure]
pub fn get_user(id: u64) -> Option<User> {
    // In a real implementation, this would query a database
    if id == 0 {
        return None;
    }
    Some(User {
        id,
        email: "test@example.com".to_string(),
        age: 25,
        created_at: 1704307200,
    })
}

/// Delete user by ID
///
/// # API Endpoint
/// DELETE /api/users/{id}
///
/// # Contracts
/// - requires: id > 0 (valid user ID)
/// - effects: IO (database modification)
#[trust::requires("id > 0")]
#[trust::effects(IO)]
#[trust::api(path = "/api/users/{id}", method = "DELETE")]
pub fn delete_user(id: u64) -> Result<(), ApiError> {
    if id == 0 {
        return Err(ApiError::InternalError);
    }
    // In a real implementation, this would delete from database
    Ok(())
}

/// Calculate user age from birth year
///
/// # Contracts
/// - requires: birth_year > 1900 && birth_year <= current_year
/// - ensures: result >= 0
/// - pure (no side effects)
#[trust::requires("birth_year > 1900")]
#[trust::requires("birth_year <= current_year")]
#[trust::ensures("result >= 0")]
#[trust::pure]
pub fn calculate_age(birth_year: u32, current_year: u32) -> u32 {
    current_year - birth_year
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_user_valid() {
        let result = create_user("test@example.com".to_string(), 25);
        assert!(result.is_ok());
        let user = result.unwrap();
        assert!(user.id > 0);
        assert_eq!(user.age, 25);
    }

    #[test]
    fn test_create_user_underage() {
        let result = create_user("test@example.com".to_string(), 17);
        assert!(matches!(result, Err(ApiError::UnderageUser)));
    }

    #[test]
    fn test_create_user_empty_email() {
        let result = create_user("".to_string(), 25);
        assert!(matches!(result, Err(ApiError::InvalidEmail)));
    }

    #[test]
    fn test_get_user_valid() {
        let result = get_user(1);
        assert!(result.is_some());
        assert_eq!(result.unwrap().id, 1);
    }

    #[test]
    fn test_get_user_invalid() {
        let result = get_user(0);
        assert!(result.is_none());
    }
}
