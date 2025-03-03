#[macro_export]
macro_rules! gpp_error {
    ($($arg:tt)*) => {
        {
            eprintln!("\x1b[31mError\x1b[0m: {}", format_args!($($arg)*));
            std::process::exit(1);
        }
    };
}
