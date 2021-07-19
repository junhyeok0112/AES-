#include<iostream>
#include<iomanip>
#include<fstream>
#include<bitset>

#define ROTL8(x,shift) ((uint8_t) ((x) << (shift)) | ((x) >> (8 - (shift))))

using namespace std;

typedef unsigned char uc;
typedef unsigned int ui;

const uc poly = 0xE7, sboxAdd = 0x63, lsboxadd = 0x05;	//거꾸로 되어 있음 즉 밑에서부터 ->동영상 참고

const uc sboxArray[] = { 0xF1 ,0xE3 , 0xC7 , 0x8F ,0x1F, 0x3E, 0x7C, 0xF8 };//얘는 정방향 , 방향 잘보고하기;
const uc IsboxArray[] = { 0xA4 , 0x49, 0x92,0x25, 0x4A, 0x94, 0x29, 0x52 };

const uc mixArray[4][4] = { {0x02, 0x03,0x01,0x01},{0x01, 0x02, 0x03, 0x01}, {0x01, 0x01, 0x02, 0x03 }, { 0x03, 0x01, 0x01, 0x02 } };
const uc ImixArray[4][4] = { {0x0E,0x0B,0x0D,0x09},{0x09,0x0E,0x0B,0x0D},{0x0D,0x09,0x0E,0x0B},{0x0B , 0x0D , 0x09 ,0x0E} };

uc key[16], roundKey[176], plainText[4][4], cipherText[4][4];

int Nr = 10, Nk = 4, Nb = 4;


//차수 구하기
uc deg(unsigned short num)
{
	uc i;
	for (i = 0; i <= 8; i++)
	{
		if (!(num >> (i + 1)))
		{
			return i;
		}
	}
}

// a/b
uc divide(unsigned short a, uc b, uc& r)	//
{
	uc a_deg = deg(a);
	uc b_deg = deg(b);
	if (a < b)
	{
		r = a;
		return 0;
	}
	uc bit = a_deg - b_deg;
	unsigned short temp = b;
	temp = temp << bit;
	a = a ^ temp;
	return (1 << bit) | divide(a, b, r);
}


uc multiply(uc a, uc b)
{
	uc res = 0;
	if (b & 0x01)
	{
		res = a;
	}
	for (uc i = 1; i < 8; i++)
	{
		if (b & (0x01 << i))
		{
			uc temp = a;
			for (uc j = 0; j < i; j++)
			{
				if (!(temp & 0x80))
				{
					temp <<= 1;
				}
				else
				{
					temp <<= 1;
					temp = temp ^ 0xE7;		//변경된 AES의 다항식의 
				}
			}
			res = res ^ temp;
		}
	}
	return res;
}

uc inverse(uc b)		//다항식의 역원 구하기
{
	if (b == 0)
		return 0;

	short r0 = 0x1E7;
	uc r1 = b, r2, q;
	uc w0 = 0, w1 = 1, w2;
	q = divide(r0, r1, r2);
	w2 = w0 ^ multiply(q, w1);
	while (1)
	{
		
		if (r2 == 0)
			break;
		r0 = r1;
		r1 = r2;
		q = divide(r0, r1, r2);
		w0 = w1;
		w1 = w2;
		w2 = w0 ^ multiply(q, w1);
	}
	return w1;
}


uc map(uc a)	//다항식 역원 구한 값 SBox 매핑시켜서 값 내기
{
	// SBox mapping 해주는 공식 존재. 
	// SBox 함수 적용 해주는 공식
	// b′i=bi⊕b(i+4)mod8⊕b(i+5)mod8⊕b(i+6)mod8⊕b(i+7)mod8⊕ci
	uc c = 0x63;
	uc res = 0x0;
	uc temp = 0x0;
	uc i;
	for (i = 0; i < 8; i++)
	{
		//역원값 sbox 행렬계산하는 과정 
		temp = temp ^ ((a >> i) & 0x1) ^ ((a >> ((i + 4) % 8)) & 0x1);
		temp = temp ^ ((a >> ((i + 5) % 8)) & 0x1) ^ ((a >> ((i + 6) % 8)) & 0x1);
		temp = temp ^ ((a >> ((i + 7) % 8)) & 0x1) ^ ((c >> i) & 0x1);
		res = res | (temp << i);
		temp = 0x0;
	}
	return res;
}


void SubBytes(uc state[][4])	//암호화 과정에서 subbyte 과정
{
	int i, j;
	unsigned char t;
	for (i = 0; i < 4; i++)
	{
		for (j = 0; j < 4; j++)
		{
			t = state[i][j];
			state[i][j] = map(inverse(t));	//들어온 다항식 T역원 구해서 SBox 값 매핑해줌
		}
	}

}	

void ShiftRow(uc state[][4], int i, int n)    //암호화 과정에서 열 바꿔주기
{
	unsigned char* tmp = new unsigned char[4];
	for (int j = 0; j < 4; j++) {
		tmp[j] = state[i][(j + n) % 4];
	}
	memcpy(state[i], tmp, 4 * sizeof(unsigned char));

	delete[] tmp;
}

void ShiftRows(uc state[][4])
{
	//암호화 과정에서 열 바꿔주기
	ShiftRow(state, 1, 1);
	ShiftRow(state, 2, 2);
	ShiftRow(state, 3, 3);
}

void MixSingleColumn(unsigned char* r)
{
	unsigned char a[4];
	unsigned char b[4];
	unsigned char c;
	unsigned char h;
	
	for (c = 0; c < 4; c++)
	{
		a[c] = r[c];
		
		h = (unsigned char)((signed char)r[c] >> 7); 
		b[c] = r[c] << 1; 
		b[c] ^= 0xE7 & h;  //다항식 변경해서 mixColumn 적용
	}
	r[0] = b[0] ^ a[3] ^ a[2] ^ b[1] ^ a[1]; 
	r[1] = b[1] ^ a[0] ^ a[3] ^ b[2] ^ a[2];
	r[2] = b[2] ^ a[1] ^ a[0] ^ b[3] ^ a[3]; 
	r[3] = b[3] ^ a[2] ^ a[1] ^ b[0] ^ a[0]; 
}



void MixColumns(uc state[][4])
{//암호화 과정에서 MixColumns
	unsigned char* temp = new unsigned char[4];

	for (int i = 0; i < 4; ++i)
	{
		for (int j = 0; j < 4; ++j)
		{
			temp[j] = state[j][i]; 
		}
		MixSingleColumn(temp); 
		for (int j = 0; j < 4; ++j)
		{
			state[j][i] = temp[j]; 
		}
	}
	delete[] temp;
}



void AddRoundKey(uc state[][4], unsigned char* key)		//AddRoundKey -> XOR 연산
{
	int i, j;
	for (i = 0; i < 4; i++)
	{
		for (j = 0; j < 4; j++)
		{
			state[i][j] = state[i][j] ^ key[i + 4 * j];
		}
	}
}

//키확장에 사용되는 메소드들
unsigned char xtime(unsigned char b)    // 주어진 다항식 X 곱하기
{
	return (b << 1) ^ (((b >> 7) & 1) * 0xE7);
}

void SubWord(unsigned char* a)
{
	//SBox 대응해주기
	int i;
	for (i = 0; i < 4; i++)
	{
		a[i] = map(inverse(a[i]));
	}
}

void RotWord(unsigned char* a)
{	//단어 rotate시키기
	unsigned char c = a[0];
	a[0] = a[1];
	a[1] = a[2];
	a[2] = a[3];
	a[3] = c;
}

void XorWords(unsigned char* a, unsigned char* b, unsigned char* c)
{
	int i;
	for (i = 0; i < 4; i++)
	{
		c[i] = a[i] ^ b[i];
	}
}

void Rcon(unsigned char* a, int n)
{
	int i;
	unsigned char c = 1;
	for (i = 0; i < n - 1; i++)
	{
		c = xtime(c);
	}

	a[0] = c;
	a[1] = a[2] = a[3] = 0;
}

void KeyExpansion(unsigned char key[], unsigned char w[])
{
	//키 확장 메소드
	unsigned char* temp = new unsigned char[4];
	unsigned char* rcon = new unsigned char[4];
	//w에 roundKey 배열 저장 .
	
	int i = 0;
	//key에 있는 값들 roundKey 배열에 저장 
	while (i < 4 * Nk)
	{
		w[i] = key[i];
		i++;
	}

	i = 4 * Nk;
	//roundKey 키 확장
	while (i < 4 * 4 * (Nr + 1))
	{
		temp[0] = w[i - 4 + 0];
		temp[1] = w[i - 4 + 1];
		temp[2] = w[i - 4 + 2];
		temp[3] = w[i - 4 + 3];

		if (i / 4 % Nk == 0)
		{
			RotWord(temp);
			SubWord(temp);
			Rcon(rcon, i / (Nk * 4));
			XorWords(temp, rcon, temp);
		}
		else if (Nk > 6 && i / 4 % Nk == 4)
		{
			SubWord(temp);
		}

		w[i + 0] = w[i - 4 * Nk] ^ temp[0];
		w[i + 1] = w[i + 1 - 4 * Nk] ^ temp[1];
		w[i + 2] = w[i + 2 - 4 * Nk] ^ temp[2];
		w[i + 3] = w[i + 3 - 4 * Nk] ^ temp[3];
		i += 4;
	}

	delete[]rcon;
	delete[]temp;

}

void cout_ciphertext(int cnt) {	//암호문 출력 
	cout << cnt << "번째";
	for (int i = 0; i < 16; i++) {
		cout << " " << hex << uppercase << setfill('0') << setw(2) << static_cast<int>(cipherText[i % 4][i / 4]);
	}
	cout << endl;

}

void cout_plaintext(int cnt) {	//입력문 출력
	cout << cnt << "번째";
	for (int i = 0; i < 16; i++) {
		cout << " " << hex << uppercase << setfill('0') << setw(2) << static_cast<int>(plainText[i % 4][i / 4]);
	}
	cout << endl;

}

void Encryption(unsigned  char* roundKeys)
{
	//암호화 과정
	AddRoundKey(plainText, roundKeys);	//XOR 하고 시작 

	for (int round = 1; round <= 9; round++)
	{
		//암호화 과정 
		SubBytes(plainText);
		ShiftRows(plainText);
		MixColumns(plainText);
		AddRoundKey(plainText, roundKeys + round * 16);
		
	}

	SubBytes(plainText);
	ShiftRows(plainText);
	AddRoundKey(plainText, roundKeys + 160);

	for (int i = 0; i < 4; i++)
	{
		for (int j = 0; j < 4; j++)
		{
			cipherText[i][j] = plainText[i][j];		//변경한 Plain Text 암호문배열에 저장 
		}
	}
	

}

void inversesbox(uc state[][4]) {//inverse sbox 생성
	int hang[8][8] = //sbox 생성시 사용했던 상수 행렬의 역행렬.
	{ 0,0,1,0,0,1,0,1,
		1,0,0,1,0,0,1,0,
		0,1,0,0,1,0,0,1,
		1,0,1,0,0,1,0,0,
		0,1,0,1,0,0,1,0,
		0,0,1,0,1,0,0,1,
		1,0,0,1,0,1,0,0,
		0,1,0,0,1,0,1,0 };
	for (int n = 0; n < 4; n++) {//16*16의 inverse_sbox 행렬 생성.
		for (int m = 0; m < 4; m++) {
			uc cc = state[n][m];
			bitset <8> a = cc;
			int b[8];
			int c[8] = { 0, };
			for (int i = 0; i < 8; i++) {
				b[i] = a[i];
			}
			bitset <8> temp;
			bitset <8> d = 0b10100000;//0x15와 hang 배열(상수)의 연산값.
			int temp1[8];
			for (int t = 0; t < 8; t++) {	//거꾸로 셋팅
				temp1[7 - t] = d[t];
			}
			for (int i = 0; i < 8; i++) {
				for (int j = 0; j < 8; j++) {//역행렬과 해당 값을 연산.
					c[i] ^= (b[j] & hang[i][j]);
				}
				temp[i] = (temp1[i] ^ c[i]);
			}
			state[n][m] = inverse(temp.to_ulong());//결과값의 역원을 찾아서 저장.
		}
	}
}

unsigned char mul_bytes(unsigned char a, unsigned char b) //a와 b galios field에서 곱하기
{	//InvMixColumns에서 사용한다 
	unsigned char p = 0;
	unsigned char high_bit_mask = 0x80;
	unsigned char high_bit = 0;
	unsigned char modulo = 0xE7;	//변경된 다항식 


	for (int i = 0; i < 8; i++) {
		if (b & 1) {
			p ^= a;
		}

		high_bit = a & high_bit_mask;
		a <<= 1;
		if (high_bit) {
			a ^= modulo;
		}
		b >>= 1;
	}

	return p;
}


void InvMixColumns(uc state[][4])
{	//역 MixColumns 진행 
	unsigned char s[4], s1[4];
	int i, j;

	for (j = 0; j < Nb; j++)
	{
		for (i = 0; i < 4; i++)
		{
			s[i] = state[i][j];
		}
		s1[0] = mul_bytes(0x0e, s[0]) ^ mul_bytes(0x0b, s[1]) ^ mul_bytes(0x0d, s[2]) ^ mul_bytes(0x09, s[3]);
		s1[1] = mul_bytes(0x09, s[0]) ^ mul_bytes(0x0e, s[1]) ^ mul_bytes(0x0b, s[2]) ^ mul_bytes(0x0d, s[3]);
		s1[2] = mul_bytes(0x0d, s[0]) ^ mul_bytes(0x09, s[1]) ^ mul_bytes(0x0e, s[2]) ^ mul_bytes(0x0b, s[3]);
		s1[3] = mul_bytes(0x0b, s[0]) ^ mul_bytes(0x0d, s[1]) ^ mul_bytes(0x09, s[2]) ^ mul_bytes(0x0e, s[3]);

		for (i = 0; i < 4; i++)
		{
			state[i][j] = s1[i];
		}
	}
}

void InvShiftRows(uc state[][4])
{
	ShiftRow(state, 1, Nb - 1);
	ShiftRow(state, 2, Nb - 2);
	ShiftRow(state, 3, Nb - 3);
}

void Descrpytion(unsigned  char* roundKeys)
{
	//복호화 과정

	AddRoundKey(cipherText, roundKeys + 160);
	cout << "첫번째 ARK : ";
	cout_ciphertext(0);
	for (int round = 9; round >= 1; round--)
	{


		InvShiftRows(cipherText);
		cout << "ISR : ";
		cout_ciphertext(round);
		inversesbox(cipherText);
		cout << "ISB : ";
		cout_ciphertext(10);
		AddRoundKey(cipherText, roundKeys + round * 16);
		cout << "ARK : ";
		cout_ciphertext(round);
		InvMixColumns(cipherText);
		cout << "IMC: ";
		cout_ciphertext(round);
	}



	InvShiftRows(cipherText);
	cout << "ISR : ";
	cout_ciphertext(10);
	inversesbox(cipherText);
	cout << "ISB : ";
	cout_ciphertext(10);
	AddRoundKey(cipherText, roundKeys);
	cout << "ARK : ";
	cout_ciphertext(10);

	for (int i = 0; i < 4; i++)
	{
		for (int j = 0; j < 4; j++) {
			plainText[i][j] = cipherText[i][j];
		}
	}



}


int main() {



	//cout << hex << static_cast<int>(inversesbox(0x6E)) << endl;

	ifstream keyFile;

	keyFile.open("key.bin", ios::binary);
	if (!keyFile.is_open()) {
		cout << "key.bin is not open" << endl;
		return -1;
	}

	keyFile.read((char*)key, 16);

	KeyExpansion(key, roundKey);

	//KEY expansion 끝
	cout << "expended key:" << endl;
	for (int i = 0; i <= 10; i++) {
		cout << "k" << dec << i << ":";
		for (int j = 0; j < 16; j++) {
			//keyExpansion 확인 과정
			cout << " " << hex << uppercase << setfill('0') << setw(2) << static_cast<int>(roundKey[j + (i * 16)]);

		}
		cout << endl;
	}

	char exec;
	cout << "e or d : ";
	cin >> exec;

	ifstream plainFile("plain.bin", ios::binary);

	if (exec == 'e') {
		ifstream plainFile("plain.bin", ios::binary);
		if (!plainFile.is_open()) {
			cout << "plain.bin is not open" << endl;
			return -1;
		}

		uc buf[16];
		int i = 1;
		while (plainFile.read((char*)buf, 16)) {
			for (int i = 0; i < 16; i++) {
				plainText[i % 4][i / 4] = buf[i];
			}


			Encryption(roundKey);	//라운드 키 이용해서 암호화


			//cout_ciphertext(i++);

			ofstream cipherFile("cipher.bin", ios::binary | ios::app);
			cipherFile << cipherText[0][0] << cipherText[1][0] << cipherText[2][0] << cipherText[3][0]
				<< cipherText[0][1] << cipherText[1][1] << cipherText[2][1] << cipherText[3][1]
				<< cipherText[0][2] << cipherText[1][2] << cipherText[2][2] << cipherText[3][2]
				<< cipherText[0][3] << cipherText[1][3] << cipherText[2][3] << cipherText[3][3];

			cout << endl;
		}

	}
	else if (exec == 'd') {
		ifstream cipherFile("cipher.bin", ios::binary);
		if (!cipherFile.is_open()) {
			cout << "cipher.bin is not open" << endl;
			return -1;
		}

		uc buf[16];
		int i = 1;
		while (cipherFile.read((char*)buf, 16)) {
			for (int i = 0; i < 16; i++) {
				cipherText[i % 4][i / 4] = buf[i];
			}

			Descrpytion(roundKey);

			cout_plaintext(i++);
			//InvSub 값 바꾸기 

			ofstream plainFile2("plain2.bin", ios::binary | ios::app);
			plainFile2 << plainText[0][0] << plainText[1][0] << plainText[2][0] << plainText[3][0]
				<< plainText[0][1] << plainText[1][1] << plainText[2][1] << plainText[3][1]
				<< plainText[0][2] << plainText[1][2] << plainText[2][2] << plainText[3][2]
				<< plainText[0][3] << plainText[1][3] << plainText[2][3] << plainText[3][3];

		}

	}


	return 0;
}