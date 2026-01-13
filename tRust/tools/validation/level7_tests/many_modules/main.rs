mod mod_a;
mod mod_b;
mod mod_c;
mod mod_d;
mod mod_e;
mod mod_f;
mod mod_g;
mod mod_h;

fn main() {
    println!("Sum: {}",
        mod_a::value() + mod_b::value() + mod_c::value() + mod_d::value() +
        mod_e::value() + mod_f::value() + mod_g::value() + mod_h::value()
    );
}
