ENTRY(_start)

MEMORY
{
  RAM (rwx) : ORIGIN = 0x00000000, LENGTH =4K
}

SECTIONS
{
  .init : {
    *(.init)
} > RAM

  .text : {
    *(.text*)
    *(.rodata*)
  } > RAM

  .data : {
    *(.data*)
  } > RAM

  .bss : {
    *(.bss*)
    *(COMMON)
  } > RAM

.stack (NOLOAD) : {
    PROVIDE(_stack_top = ORIGIN(RAM) + LENGTH(RAM));
} > RAM

}
