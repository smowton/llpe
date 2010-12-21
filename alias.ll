@open = alias i32 (i8*, i32, ...)* @__wrap_open

declare i32 @__wrap_open(i8*, i32, ...)

@read = alias i32 (i32, i8*, i64)* @__wrap_read

declare i32 @__wrap_read(i32, i8*, i64)

@close = alias i32 (i32)* @__wrap_close

declare i32 @__wrap_close(i32)