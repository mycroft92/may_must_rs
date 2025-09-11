; Function declaration for printf
declare i32 @printf(i8*, ...)

; Global string constant for output
@output_fmt = private constant [18 x i8] c"Result value: %d\0A\00"

define i32 @indirect_branch_example(i8* %addr) {
entry:
  %block1_addr = bitcast i8* blockaddress(@indirect_branch_example, %block1) to i8*
  %block2_addr = bitcast i8* blockaddress(@indirect_branch_example, %block2) to i8*
  %block3_addr = bitcast i8* blockaddress(@indirect_branch_example, %block3) to i8*
  
  indirectbr i8* %addr, [ label %block1, label %block2, label %block3 ]

block1:
  ret i32 1

block2:
  ret i32 2

block3:
  ret i32 3
}

define i32 @main() {
entry:
  ; Get the addresses of blocks using bitcast
  %addr1 = bitcast i8* blockaddress(@indirect_branch_example, %block1) to i8*
  
  ; Call the function with block1's address
  %result1 = call i32 @indirect_branch_example(i8* %addr1)
  
  ; Print the result
  %printf_args1 = getelementptr [18 x i8], [18 x i8]* @output_fmt, i32 0, i32 0
  call i32 (i8*, ...) @printf(i8* %printf_args1, i32 %result1)
  
  ; Try with block2
  %addr2 = bitcast i8* blockaddress(@indirect_branch_example, %block2) to i8*
  %result2 = call i32 @indirect_branch_example(i8* %addr2)
  call i32 (i8*, ...) @printf(i8* %printf_args1, i32 %result2)
  
  ; Try with block3
  %addr3 = bitcast i8* blockaddress(@indirect_branch_example, %block3) to i8*
  %result3 = call i32 @indirect_branch_example(i8* %addr3)
  call i32 (i8*, ...) @printf(i8* %printf_args1, i32 %result3)
  
  ret i32 0
}
