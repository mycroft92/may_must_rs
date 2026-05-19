#include "local_assert.h"

int main()
{
  unsigned int SIZE = 1;
  unsigned int j;
  int array[SIZE], menor;

  menor = nondet_int();

  for (j = 0; j < SIZE; j++) {
    array[j] = nondet_int();
    if (array[j] <= menor)
      menor = array[j];
  }

  may_assert(array[0] >= menor);

  return 0;
}
