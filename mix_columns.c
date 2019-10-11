#include <stdio.h>

int main(int argc, char** argv) {
    unsigned char r[4];
    unsigned char a[4];
    unsigned char b[4];
    unsigned char c;
    unsigned char h;

	unsigned s0,s1,s2,s3;
	unsigned t0,t1,t2,t3;

	unsigned char b0,b1,b2,b3;
	unsigned char ss0, ss1, ss2, ss3;

		s0 = 133;   r[0] = s0;
		s1 = 144;   r[1] = s1;
		s2 = 127; r[2] = s2;
		s3 = 128; r[3] = s3;

		b0 = (s0 << 1) ^ (0x1B & ((s0 >> 7) * 255));
		b1 = (s1 << 1) ^ (0x1B & ((s1 >> 7) * 255));
		b2 = (s2 << 1) ^ (0x1B & ((s2 >> 7) * 255));
		b3 = (s3 << 1) ^ (0x1B & ((s3 >> 7) * 255));


//		printf("%u\n", ((unsigned char)((signed char)s3 >> 7)));
//		printf("%u\n", ((unsigned char)(             s3 >> 7)));


		t0 = (s0 << 1) ^ s1 ^ (s1 << 1) ^ s2 ^ s3;
		t1 = s0 ^ (s1 << 1) ^ s2 ^ (s2 << 1) ^ s3;
		t2 = s0 ^ s1 ^ (s2 << 1) ^ s3 ^ (s3 << 1);
		t3 = s0 ^ (s0 << 1) ^ s1 ^ s2 ^ (s3 << 1);

		ss0 = b0 ^ s1 ^ b1 ^ s2 ^ s3;
		ss1 = s0 ^ b1 ^ s2 ^ b2 ^ s3;
		ss2 = s0 ^ s1 ^ b2 ^ s3 ^ b3;
		ss3 = s0 ^ b0 ^ s1 ^ s2 ^ b3;

		s0 = t0 ^ ((unsigned)(-(int)(t0 >> 7)) & 0x1B);
		s1 = t1 ^ ((unsigned)(-(int)(t1 >> 7)) & 0x1B);
		s2 = t2 ^ ((unsigned)(-(int)(t2 >> 7)) & 0x1B);
		s3 = t3 ^ ((unsigned)(-(int)(t3 >> 7)) & 0x1B);




    /* The array 'a' is simply a copy of the input array 'r'
     * The array 'b' is each element of the array 'a' multiplied by 2
     * in Rijndael's Galois field
     * a[n] ^ b[n] is element n multiplied by 3 in Rijndael's Galois field */ 
    for (c = 0; c < 4; c++) {
        a[c] = r[c];
        /* h is 0xff if the high bit of r[c] is set, 0 otherwise */
        h = (unsigned char)((signed char)r[c] >> 7); /* arithmetic right shift, thus shifting in either zeros or ones */
        b[c] = r[c] << 1; /* implicitly removes high bit because b[c] is an 8-bit char, so we xor by 0x1b and not 0x11b in the next line */
        b[c] ^= 0x1B & h; /* Rijndael's Galois field */
    }
    r[0] = b[0] ^ a[3] ^ a[2] ^ b[1] ^ a[1]; /* 2 * a0 + a3 + a2 + 3 * a1 */
    r[1] = b[1] ^ a[0] ^ a[3] ^ b[2] ^ a[2]; /* 2 * a1 + a0 + a3 + 3 * a2 */
    r[2] = b[2] ^ a[1] ^ a[0] ^ b[3] ^ a[3]; /* 2 * a2 + a1 + a0 + 3 * a3 */
    r[3] = b[3] ^ a[2] ^ a[1] ^ b[0] ^ a[0]; /* 2 * a3 + a2 + a1 + 3 * a0 */

    printf("%u\n", s0);
    printf("%u\n", ss0);
    printf("%u\n", r[0]);
    printf("\n");

    printf("%u\n", s1);
    printf("%u\n", ss1);
    printf("%u\n", r[1]);
    printf("\n");

    printf("%u\n", s2);
    printf("%u\n", ss2);
    printf("%u\n", r[2]);
    printf("\n");

    printf("%u\n", s3);
    printf("%u\n", ss3);
    printf("%u\n", r[3]);
    printf("\n");

	return 0;
}
