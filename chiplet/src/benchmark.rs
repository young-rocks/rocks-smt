//use std::time::Instant;

//#[macro_export]
#[cfg(test)]
mod test {
    macro_rules! measure {
        ($task:block, $backend:expr, $task_name:expr, $num_iter:expr) => {
            let start = Instant::now();
            for _ in 0..($num_iter - 1) {
                $task;
            }
            let res = $task;
            let end = start.elapsed();
            println!(
                "{}: Average {} time: {:?}",
                $backend,
                $task_name,
                end / $num_iter
                );
            res
        };
    }
}

//fn test() -> u32 {
//    1
//}
//pub fn test_measure() {
//    let r = measure!({test()}, "2", "3", 4);
//    println!("test {}", r);
//}
