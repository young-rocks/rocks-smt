//use std::time::Instant;

#[cfg(test)]
mod test {
    #[macro_export]
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
