//void main() {    
// register unsigned int x1 asm("x1") = 12;     // Simulated return address
//     register unsigned int x2 asm("x2") = 4096;   // Simulated stack pointer
//     register unsigned int x3 asm("x3");          // Will hold x2 + x1
//     register unsigned int a0 asm("a0");          // Return value

//     asm volatile (
//         "add x3, x2, x1\n"   // x3 = x2 + x1
//         "mv a0, x3\n"        // a0 = x3
//         "ebreak\n"           // halt for debug
//     );
// }


// Example: tst.c
//int main() {
   
  //  int b = 5;
  //  int c;

 //   c=b+2;
    
  //  return (b+c); // Final result will be 0
//}


int main() {
    int a = 1;
    int b = 0;
    for (a = 1; a <= 4; a++) {
        b = b + a;
    }
    return b; // Final result will be 10
}



//#define LED_ADDR 0x0c  // Replace with actual GPIO address

//void main() {
  //  volatile unsigned int *led = (unsigned int *)LED_ADDR;

   // while (1) {
      //  *led = 0xFF;  // Turn on LEDs
        //for (volatile int i = 0; i < 100000; i++);  // Delay
      //  *led = 0x00;  // Turn off LEDs
    //    for (volatile int i = 0; i < 100000; i++);  // Delay
  //  }
//}
