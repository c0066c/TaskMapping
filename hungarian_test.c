/********************************************************************
 ********************************************************************
 **
 ** libhungarian by Cyrill Stachniss, 2004
 **
 **
 ** Solving the Minimum Assignment Problem using the 
 ** Hungarian Method.
 **
 ** ** This file may be freely copied and distributed! **
 **
 ** Parts of the used code was originally provided by the 
 ** "Stanford GraphGase", but I made changes to this code.
 ** As asked by  the copyright node of the "Stanford GraphGase", 
 ** I hereby proclaim that this file are *NOT* part of the
 ** "Stanford GraphGase" distrubition!
 **
 ** This file is distributed in the hope that it will be useful,
 ** but WITHOUT ANY WARRANTY; without even the implied 
 ** warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR
 ** PURPOSE.  
 **
 ********************************************************************
 ** CODES-VP paper, 2015 KHChen.
 ** Integrate the Hungarian Method with version selection.
 ********************************************************************
 ********************************************************************/


#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <sys/time.h>
#include <mach/clock.h>
#include <mach/mach.h>
#include <math.h>
#include "hungarian.h"
#define X 7
#define Y 7 // the allowed number of RMT <- free cores.

void generateMesh();

/*Random Generation Parameters*/
double W=0.3;
double microsec_sum=0.0;
double max_sec = 0.0;
double SD=0.01; //standard distance

/*Testing Mode*/
/*0,0,0 is for uniform distribution
 *1,1,0 is for BIG.little
 *0,0,1 is for normal distribution*/
#define constant 0 //group speed Big.little should open this
#define speed_level 0 //for group speed Big.little be 1
#define normal_dis 0 // normal distribution should be 1, uniform distribution should be 0

#define dependency 0 //dependency on/off
#define referToFast 1 //reference to fastest core or slowest core
#define givenType 1 //given Type
//int lambda[X]={1,1,1,1,1,1,1}; //seven tasks 1 = TMR, 0=NR
int lambda[X]={};
int exchange[X]={64,32,16,8,4,2,1};


/*Enviroment Setting*/
int alphascale = 1000; //without scale
int size[X]={4, 4, 2, 3, 1, 2, 5}; //version size
int deadline[X]={90,10,10,35,80,39,80}; //PA input deadline
//int deadline[X]={100,10,10,35,80,40,80}; //testing input deadline
//int deadline[X]={80,10,10,36,28,39,50}; //tighter deadline 160% avg et
//int deadline[X]={100,10,10,45,34,49,64}; //loose deadline 200% avg et

/*dependencies setting*/
//SAD,SATD,DCT,SUSAN,CRC,ADPCM,SHA
int piRef[X]={1,1,0,0,1,0,1}; //task has a predecessor = 1;
int outputSize[X]={1024,64,64,12000,4,28000,4};
int inputSize[X]={1024,64,64,12000,28000,110000,28000};
int mu=5; //hop required cycles
int meshPosition[49]={
		12,11,10,9,10,11,12,
		11,10,9,8,9,10,11,
		10,9,8,7,8,9,10,
		9,8,7,6,7,8,9,
		10,9,8,7,8,9,10,
		11,10,9,8,9,10,11,
		12,11,10,9,10,11,12};

int checkList[X]={0,0,0,0,0,0,0};
//int dataSize[X]={98,2,2,26,50,80,95};
//int hopsCycle=2;

/*Testing Parameters*/
double timing_constraint=0.15; //deadline missrate constraint.
float alpha = 0.1; //在DAC我可能不是用0.5
int Rscale = 1000; //10^-6-10^-7
int verbose=0;

/*Global initialization*/
int BF_flag=0; //flag for checking whether this is the first time to test;
int dTune_res=-1; //danger
int BF_res=-1; //danger
int maxIndex=-1;
int delta=0, lamd=0;
int ARBIT = 0;
int n_nr=0, n_tmr=0;
int pro_order[X]={};
double slowestFrequency=0.0;

int **seltable, **dtunetable, **MP_cores, **final_assignment, **clone_seltable;
double **R, **AVG, ***C, ***P, ***SP;
double *frequency_scale;

/*Code Begining*/

long dtime(struct timespec start, struct timespec end)
{
	long sec, nsec;
	sec = end.tv_sec  - start.tv_sec;
 	nsec = end.tv_nsec - start.tv_nsec;
// 	fprintf(stderr, "nsec %ld, sec %ld\n", start.tv_nsec , start.tv_sec);
//	return ((sec) * 1000 + nsec/1000000); // time in milliseconds
 	return ((sec) * 1000000 + nsec/1000); // time in microseconds
}
struct dtune_task
{
  int task;
  int RTP;
};

int calculateTempDelta(int* temp){
	int d = X, nr = X, ntmr=0, i;
	for(i=0;i<X;i++){
		if(temp[i] == 1){
			d +=2;
			nr-=1;
			ntmr+=1;
		}
	}
	return d;
}
void calculateDelta(){
	int d = X, nr = X, ntmr=0, i;
	for(i=0;i<X;i++){
		if(lambda[i] == 1){
			d +=2;
			nr-=1;
			ntmr+=1;
		}
	}
	delta = d;
	n_nr = nr;
	n_tmr = ntmr;
}

double unif(double seed)
{
  double a1=3972.0,a2=4094.0;
  double m=2147483647.0;
  double seed1,seed2;
           seed1 = a1 * seed ;
           seed2 = a2 * seed ;
           /* control seed < 10^10 */
           seed1 = seed1 - (long)(seed1/m) * m ;
           seed2 = seed2 - (long)(seed2/m) * m ;
           seed = seed1 * 100.0 + seed2;
           seed = seed - (long)(seed/m)*m;

   if((seed/m)<0){
      return(-1*seed/m);}
     else
      return(seed/m);
}

double norm(double mean, double var)
{
	double sz=0.0,v1,v2,sigma,ans;
//	double seed1, seed2;
	sigma=sqrt(var);
	v1=1-((double)rand()/(RAND_MAX))*W;
	v2=1-((double)rand()/(RAND_MAX))*W;
//	seed1=rand()+clock()*123;
//	v1=unif(seed1);
//	fprintf(stderr,"V1 %lf \n", v1);
//	fprintf(stderr,"V2 %lf \n", v2);
//	seed2=fabs(clock()*1236*var+rand()-seed1);
//	v2=unif(seed2);
//	fprintf(stderr,"%lf ", v2);
	sz=cos(2*M_PI*v1)*sqrt(-2*log(v2)); //v1 and v2 are the extreme points
	ans=sz*sigma+mean;
	if(ans<(1-W))
		ans = 1-W;
	else if(ans > 1)
		ans = 1;
	return ans;
}

void normal_distribution(double SDA){
	int i;
	fprintf(stderr,"SDA = %lf\n",SDA);
	for(i=0; i<15; i++){
//		norm(0,1);
		fprintf(stderr, "%lf \n",norm(1-W,SDA));
	}
	fprintf(stderr,"\n");
}

int compare_frequency(const void* a, const void* b){
	double c = *(double *)a;
	double d = *(double *)b;
	if(c<d) {return 1;}
	else if(c==d){return 0;}
	else return -1;
}

void protection_generate(int decimal){
	int i, binary[7];
	for(i=1;i<=7;i++){
		binary[7-i]=decimal%2;
		decimal=decimal/2;
	}
	for(i=0;i<7;i++)
		lambda[i] = binary[i];
//	for(i=0;i<5;i++) //constant
//		lambda[i] = 0;

	calculateDelta();
}

int ORTP_calculated(double R, double C){ //original
	int RTPscale = 100000;
	double RTP;
//	fprintf(stderr,"RTP: R = %lf, T = %lf \n", (alpha/alphascale)*R, (1-alpha)*(1-C));
	RTP = (alpha/alphascale)*R+(1-alpha)*(1-C);//increase the penalty of T
	return (int)(RTP*RTPscale);
}

int RTP_calculated(double R, double C){
	int RTPscale = 100000;
	double RTP;
//	fprintf(stderr,"RTP: R = %lf, T = %lf \n", (alpha/alphascale)*R, (1-alpha)*(1-C));
	if((1-C)>timing_constraint){
		RTP = (alpha/alphascale)*R+(1-alpha)*(1-C);//increase the penalty of T
		return (int)(RTP*RTPscale);
	}else{
		RTP = (alpha/alphascale)*R;
		return (int)(RTP*RTPscale);
	}
}
int penalty_calculation(double R, double C){
//	double RTP = (alpha/alphascale)*R+(1-alpha)*(1-C);
	double Penalty = (alpha/alphascale)*R;
	int scale = 100000;
//	fprintf(stderr,"Penalty: R = %lf, T = %lf \n", (alpha/alphascale)*R, (1-alpha)*(1-C));
	if((1-C)>timing_constraint){ //miss deadline rate larger than constraint
//		return INF;
		return (int)500000;
	}else{
		return (int)(Penalty*scale);
	}
}
double scale_function(int func, int version, int deadline, double scale){ //return the probability of CDF(D)
	int t=0;
	double res = 0, sum = 0;
	//printf("scale func %d version %d deadline %d on core %d to scale %lf\n", func, version, deadline, core, scale);
	for(t=0;t<=1000;t++){//init SPtable
		SP[func][version][t]=0;
	}
	for(t=0;t<=100;t++){
		int k = (int)(t/scale);
//		printf("k= %d \n", k);
		if(P[func][version][t]!=0)
			SP[func][version][k]+=P[func][version][t];
//		printf("k = %d, t=%d \n",k, t);
//		if(SP[func][version][k]!=0)
//			printf("Scaled P= %lf \n",SP[func][version][k]);
		sum+=SP[func][version][k];
	}
//	printf("Total prob %lf\n", sum);
//	printf("scale C to %lf\n", scale);
#if communicate
	for(t=0;t<=deadline;t++){
		if(SP[func][version][t]!=0){
			res+=SP[func][version][t];
//			printf("SP[%d]=%lf \n",t, SP[func][version][t]);
		}
	}
#else
	for(t=0;t<=deadline;t++){
		if(SP[func][version][t]!=0){
			res+=SP[func][version][t];
//			printf("SP[%d]=%lf \n",t, SP[func][version][t]);
		}
	}
#endif
//	printf("Origin result = %lf \n",C[func][version][deadline]);
//	printf("New result = %lf \n",res);
	return res;
}
void bruteVersion(int tempDelta, int* tempLambda){
	int i, j, v;

	//delta is the demand cores of all tasks
//	calculateDelta();//delta calculation
	i=0;
	//sort the cores by the random frequencies.
	//Please note, the frequencies is determined by the outer loop for variaions
	slowestFrequency = frequency_scale[tempDelta-1];
//	fprintf(stderr,"the slowest %lf and fastest %lf \n",slowestFrequency, frequency_scale[0]);
	R = (double**)calloc(X,sizeof(double*));
	for(i=0;i<X;i++){ //for each task
		R[i]=(double*)calloc(size[i],sizeof(double));
	}
	AVG = (double**)calloc(X,sizeof(double*));
	for(i=0;i<X;i++){ //for each task
		AVG[i]=(double*)calloc(size[i],sizeof(double));
	}
	//read input part
	FILE *file = fopen("PAInput/Rij_Origin.txt", "r");
	if(!file) {
		fprintf(stderr, "Cannot open Rij\n");
//		return NULL;
	}

	//read r and avg data
	int iInd, jInd;
	double rValue, avgValue;
	while(fscanf(file,"%d\t%d\t%lf\t%lf", &iInd, &jInd, &rValue, &avgValue) != EOF){
		R[iInd][jInd]=rValue/Rscale;
		AVG[iInd][jInd]=avgValue;
//		printf("%lf\n", R[iInd][jInd]);
//		printf("%lf\n", AVG[iInd][jInd]);
	}
	fclose(file);

	//read c and calculate p
	C = (double***)calloc(X,sizeof(double**));
	for(i=0;i<X;i++){ //for each task
		C[i]=(double**)calloc(size[i],sizeof(double*));
		for(v = 0; v < size[i]; v++){
			C[i][v]=(double*)calloc(101,sizeof(double));
		}
	}
	P = (double***)calloc(X,sizeof(double**));
	for(i=0;i<X;i++){ //for each task
		P[i]=(double**)calloc(size[i],sizeof(double*));
		for(v = 0; v < size[i]; v++){
			P[i][v]=(double*)calloc(101,sizeof(double));
		}
	}
	SP = (double***)calloc(X,sizeof(double**));
	for(i=0;i<X;i++){ //for each task
		SP[i]=(double**)calloc(size[i],sizeof(double*));
		for(v = 0; v < size[i]; v++){
			SP[i][v]=(double*)calloc(1000,sizeof(double));
		}
	}

	char str2[30]={};
	char str3[2]={};
	int eSample=0,t;
	double cValue, cValueOld =0;
	for(i=0;i<X;i++){ //for each task
//		fprintf(stderr,"function %d\n",i);
		for(v = 0; v < size[i]; v++){
//			fprintf(stderr,"version %d\n",v);
			strcpy(str2,"PAInput/");
			str3[0]=48+i;
//			fprintf(stderr,"Astr3 = %s\n",str3);
			strcat(str2, str3);
			strcat(str2, "/");
			if((v/10)!=0){
				str3[0]=(48+v/10);
				strcat(str2, str3);
			}
			str3[0]=(48+(v%10));
//			fprintf(stderr,"str3 = %s, v=%d\n",str3,v);
			strcat(str2, str3);
			strcat(str2, ".txt\0");
//			fprintf(stderr,"str2 = %s\n",str2);
//			strcpy(str2,"PAInput/0/0.txt");
			if(i!=1&&i!=2&&i!=3){ //read file
				FILE *file = fopen(str2, "r");

				if(!file) {
					// file error
					fprintf(stderr, "Cannot open aa %s\n", str2);
//					return NULL;
				}
				t=0;
				cValueOld = 0;
				for(;;){
					if(fscanf(file,"%d\t%lf", &eSample, &cValue) != EOF){
						//for(;t<(int)(eSample/100000.0)&& t<=100; t++){
						for(;t<(int)(eSample/100000.0)&& t<=100; t++){
							C[i][v][t]=cValueOld;
//							fprintf(stderr, "C = %lf ",C[i][v][t]);
						}
//						fprintf(stderr,"\n");
						cValueOld = cValue;
					}
					else break;
				}

				for(;t<=100;t++){
					C[i][v][t]=1;
				}
				fclose(file);
			}else{
					for(t=0;t<=100;t++){
						if(t>=(int)(AVG[i][v]/100000.0))//depends upon the rij unit
						{
							C[i][v][t]=1;
//							printf("CDF func %d, version %d, time %d\n", i, v , t);
						}
						else
							C[i][v][t]=0;
					}

			}
		}
	}
//	printf("%d",RTP_calculated(R[0][0],C[0][0][100]));
	// Assign P(i,j,e) values important!! otherwise we cannot handle Frequency changing

	for(i=0;i<X;i++){
		for(j=0;j<size[i];j++){
			P[i][j][0] = 0;
			for(t=1;t<=100;t++){
				P[i][j][t]=C[i][j][t]-C[i][j][(t-1)];
			}
		}
	}

//	for(i=0;i<X;i++){
////	i=1;
//		fprintf(stderr,"function %d\n", i);
//		for(v=0;v<size[i];v++){
//			fprintf(stderr,"version %d\n", v);
//			for(t=0;t<100;t++)
//				fprintf(stderr,"%lf \n", C[i][v][t]);
//		}
//	}
//	printf("%d",RTP_calculated(R[0][0],C[0][0][100]));

	//it is important to change the CDF for each core beforehand


	// version seletcion part

	seltable = (int**)calloc(X,sizeof(int*));
	clone_seltable = (int**)calloc(X,sizeof(int*));
	for(i=0;i<X;i++) //for each task
	{
		seltable[i] = (int*)calloc(tempDelta,sizeof(int));
		clone_seltable[i] = (int*)calloc(tempDelta,sizeof(int));
	}
	for(i=0;i<X;i++){
		for(j=0;j<tempDelta;j++){
			seltable[i][j] = 7777777;
			clone_seltable[i][j] = 7777777;
		}
	}

//	ver = (int**)calloc(X,sizeof(int*));

#if 1
	for(i=0;i<X;i++) //for each task
	{
//		ver[i] = (int*)calloc(tempDelta,sizeof(int));
		int d;


		for(j=0;j<tempDelta;j++){// for each cores
#if dependency
		d = deadline[i]-(tempLambda[i]*outputSize[i]*mu*meshPosition[j]+piRef[i]*inputSize[i]*mu*meshPosition[j])/100000;
//		fprintf(stderr,"deadline = %d \n", (tempLambda[i]*outputSize[i]*mu*meshPosition[j]+piRef[i]*inputSize[i]*mu*meshPosition[j])/100000);
#else
		d = deadline[i];
//		fprintf(stderr,"deadline = %d \n", d);
#endif
			if(tempLambda[i] == 1){//version 0 is the fastest version with the shortest execution time
				//for RTP calculation
				clone_seltable[i][j] = RTP_calculated(0,scale_function(i,0,d,frequency_scale[j]));//RTP for dtune
				seltable[i][j] = penalty_calculation(0,scale_function(i,0,d,frequency_scale[j]));//no timing part
//				if(seltable[5][j]==0&&i==5){
////					fprintf(stderr,"tempDelta %d WTFFFFFFF task %d, version %d, core %d, frequency %lf\n", tempDelta, i, v, j, frequency_scale[j-1]);
//					fprintf(stderr,"tempDelta %d WTFFFFFFF task %d, version %d, core %d, frequency %lf\n", tempDelta, i, v, j, frequency_scale[j]);
////					fprintf(stderr,"Previous RTP %d: R = 0, T = %lf \n",RTP_calculated(0,scale_function(i,0,d,frequency_scale[j-1])), (1-alpha)*(1-scale_function(i,0,d,frequency_scale[j-1])));
//					fprintf(stderr,"RTP %d : R = 0, T = %lf \n",penalty_calculation(0,scale_function(i,0,d,frequency_scale[j])), (1-alpha)*(1-scale_function(i,0,d,frequency_scale[j])));
//					if(j!=0){
//					fprintf(stderr,"Previous RTP %d: R = 0, T = %lf \n",penalty_calculation(0,scale_function(i,0,d,frequency_scale[j-1])), (1-alpha)*(1-scale_function(i,0,d,frequency_scale[j-1])));
//					fprintf(stderr,"previous tempDelta %d WTFFFFFFF task %d, version %d, core %d, frequency %lf\n", tempDelta, i, v, j-1, frequency_scale[j-1]);
//					}
//				}
//				fprintf(stderr,"Function %d, core %d, version %d, original Cdf = %lf \n",i,j,0,C[i][0][d]);
			}
#if 1
			else{
				for(v = 0; v < size[i]; v++){
					if(RTP_calculated(R[i][v]/frequency_scale[j],scale_function(i,v,d,frequency_scale[j])) < clone_seltable[i][j]){
//						ver[i][j]=v;
						clone_seltable[i][j] = RTP_calculated(R[i][v]/frequency_scale[j],scale_function(i,v,d,frequency_scale[j]));
//						if(clone_seltable[i][j]==0)
//							fprintf(stderr,"WTFFFFFFF task %d, version %d, core %d\n", i, v, j);
					}
					if(penalty_calculation(R[i][v]/frequency_scale[j],scale_function(i,v,d,frequency_scale[j])) < seltable[i][j]){
//						ver[i][j]=v;
						seltable[i][j] = penalty_calculation(R[i][v]/frequency_scale[j],scale_function(i,v,d,frequency_scale[j]));
//						if(seltable[i][j]==0)
//							fprintf(stderr,"WTFFFFFFF task %d, version %d, core %d\n", i, v, j);
					}
				}
			}
#endif
		}
	}
//  fprintf(stderr, "Table for MP before polution\n");
//  hungarian_print_matrix(seltable,X, tempDelta);
	//till here, we will have a version selection table with the best versions
#endif
}


int** version_selection(int rows){
	int i, j, v;

	//delta is the demand cores of all tasks
//	calculateDelta();//delta calculation
	i=0;
	//sort the cores by the random frequencies.
	//Please note, the frequencies is determined by the outer loop for variaions
	slowestFrequency = frequency_scale[delta-1];
//	fprintf(stderr,"the slowest %lf and fastest %lf \n",slowestFrequency, frequency_scale[0]);
	R = (double**)calloc(rows,sizeof(double*));
	for(i=0;i<rows;i++){ //for each task
		R[i]=(double*)calloc(size[i],sizeof(double));
	}
	AVG = (double**)calloc(rows,sizeof(double*));
	for(i=0;i<rows;i++){ //for each task
		AVG[i]=(double*)calloc(size[i],sizeof(double));
	}
	//read input part
	FILE *file = fopen("PAInput/Rij_Origin.txt", "r");
	if(!file) {
	    fprintf(stderr, "Cannot open Rij\n");
	    return NULL;
	}

	//read r and avg data
	int iInd, jInd;
	double rValue, avgValue;
	while(fscanf(file,"%d\t%d\t%lf\t%lf", &iInd, &jInd, &rValue, &avgValue) != EOF){
		R[iInd][jInd]=rValue/Rscale;
		AVG[iInd][jInd]=avgValue;
//		printf("%lf\n", R[iInd][jInd]);
//		printf("%lf\n", AVG[iInd][jInd]);
	}
	fclose(file);

	//read c and calculate p
	C = (double***)calloc(rows,sizeof(double**));
	for(i=0;i<rows;i++){ //for each task
		C[i]=(double**)calloc(size[i],sizeof(double*));
		for(v = 0; v < size[i]; v++){
			C[i][v]=(double*)calloc(101,sizeof(double));
		}
	}
	P = (double***)calloc(rows,sizeof(double**));
	for(i=0;i<rows;i++){ //for each task
		P[i]=(double**)calloc(size[i],sizeof(double*));
		for(v = 0; v < size[i]; v++){
			P[i][v]=(double*)calloc(101,sizeof(double));
		}
	}
	SP = (double***)calloc(rows,sizeof(double**));
	for(i=0;i<rows;i++){ //for each task
		SP[i]=(double**)calloc(size[i],sizeof(double*));
		for(v = 0; v < size[i]; v++){
			SP[i][v]=(double*)calloc(1000,sizeof(double));
		}
	}

	char str2[30]={};
	char str3[2]={};
	int eSample=0,t;
	double cValue, cValueOld =0;
	for(i=0;i<rows;i++){ //for each task
//		fprintf(stderr,"function %d\n",i);
		for(v = 0; v < size[i]; v++){
//			fprintf(stderr,"version %d\n",v);
			strcpy(str2,"PAInput/");
			str3[0]=48+i;
//			fprintf(stderr,"Astr3 = %s\n",str3);
			strcat(str2, str3);
			strcat(str2, "/");
			if((v/10)!=0){
				str3[0]=(48+v/10);
				strcat(str2, str3);
			}
			str3[0]=(48+(v%10));
//			fprintf(stderr,"str3 = %s, v=%d\n",str3,v);
			strcat(str2, str3);
			strcat(str2, ".txt\0");
//			fprintf(stderr,"str2 = %s\n",str2);
//			strcpy(str2,"PAInput/0/0.txt");
			if(i!=1&&i!=2&&i!=3){ //read file
				FILE *file = fopen(str2, "r");

				if(!file) {
					// file error
				    fprintf(stderr, "Cannot open aa %s\n", str2);
				    return NULL;
				}
				t=0;
				cValueOld = 0;
				for(;;){
					if(fscanf(file,"%d\t%lf", &eSample, &cValue) != EOF){
						//for(;t<(int)(eSample/100000.0)&& t<=100; t++){
						for(;t<(int)(eSample/100000.0)&& t<=100; t++){
							C[i][v][t]=cValueOld;
//							fprintf(stderr, "C = %lf ",C[i][v][t]);
						}
//						fprintf(stderr,"\n");
						cValueOld = cValue;
					}
					else break;
				}

				for(;t<=100;t++){
					C[i][v][t]=1;
				}
				fclose(file);
			}else{
					for(t=0;t<=100;t++){
						if(t>=(int)(AVG[i][v]/100000.0))//depends upon the rij unit
						{
							C[i][v][t]=1;
//							printf("CDF func %d, version %d, time %d\n", i, v , t);
						}
						else
							C[i][v][t]=0;
					}

			}
		}
	}
//	printf("%d",RTP_calculated(R[0][0],C[0][0][100]));
	// Assign P(i,j,e) values important!! otherwise we cannot handle Frequency changing

	for(i=0;i<rows;i++){
		for(j=0;j<size[i];j++){
			P[i][j][0] = 0;
			for(t=1;t<=100;t++){
				P[i][j][t]=C[i][j][t]-C[i][j][(t-1)];
			}
		}
	}

//	for(i=0;i<rows;i++){
////	i=1;
//		fprintf(stderr,"function %d\n", i);
//		for(v=0;v<size[i];v++){
//			fprintf(stderr,"version %d\n", v);
//			for(t=0;t<100;t++)
//				fprintf(stderr,"%lf \n", C[i][v][t]);
//		}
//	}
//	printf("%d",RTP_calculated(R[0][0],C[0][0][100]));

	//it is important to change the CDF for each core beforehand


	// version seletcion part

	seltable = (int**)calloc(rows,sizeof(int*));
	clone_seltable = (int**)calloc(rows,sizeof(int*));
	for(i=0;i<rows;i++) //for each task
	{
		seltable[i] = (int*)calloc(delta,sizeof(int));
		clone_seltable[i] = (int*)calloc(delta,sizeof(int));
	}
	for(i=0;i<X;i++){
		for(j=0;j<delta;j++){
			seltable[i][j] = 7777777;
			clone_seltable[i][j] = 7777777;
		}
	}

//	ver = (int**)calloc(rows,sizeof(int*));

#if 1
	for(i=0;i<rows;i++) //for each task
	{
//		ver[i] = (int*)calloc(delta,sizeof(int));
		int d;


		for(j=0;j<delta;j++){// for each cores
#if dependency
		d = deadline[i]-(lambda[i]*outputSize[i]*mu*meshPosition[j]+piRef[i]*inputSize[i]*mu*meshPosition[j])/100000;
//		fprintf(stderr,"deadline = %d \n", (lambda[i]*outputSize[i]*mu*meshPosition[j]+piRef[i]*inputSize[i]*mu*meshPosition[j])/100000);
#else
		d = deadline[i];
//		fprintf(stderr,"deadline = %d \n", d);
#endif
			if(lambda[i] == 1){//version 0 is the fastest version with the shortest execution time
				//for RTP calculation
				clone_seltable[i][j] = RTP_calculated(0,scale_function(i,0,d,frequency_scale[j]));//RTP for dtune
				seltable[i][j] = penalty_calculation(0,scale_function(i,0,d,frequency_scale[j]));//no timing part
//				if(seltable[5][j]==0&&i==5){
////					fprintf(stderr,"delta %d WTFFFFFFF task %d, version %d, core %d, frequency %lf\n", delta, i, v, j, frequency_scale[j-1]);
//					fprintf(stderr,"delta %d WTFFFFFFF task %d, version %d, core %d, frequency %lf\n", delta, i, v, j, frequency_scale[j]);
////					fprintf(stderr,"Previous RTP %d: R = 0, T = %lf \n",RTP_calculated(0,scale_function(i,0,d,frequency_scale[j-1])), (1-alpha)*(1-scale_function(i,0,d,frequency_scale[j-1])));
//					fprintf(stderr,"RTP %d : R = 0, T = %lf \n",penalty_calculation(0,scale_function(i,0,d,frequency_scale[j])), (1-alpha)*(1-scale_function(i,0,d,frequency_scale[j])));
//					if(j!=0){
//					fprintf(stderr,"Previous RTP %d: R = 0, T = %lf \n",penalty_calculation(0,scale_function(i,0,d,frequency_scale[j-1])), (1-alpha)*(1-scale_function(i,0,d,frequency_scale[j-1])));
//					fprintf(stderr,"previous delta %d WTFFFFFFF task %d, version %d, core %d, frequency %lf\n", delta, i, v, j-1, frequency_scale[j-1]);
//					}
//				}
//				fprintf(stderr,"Function %d, core %d, version %d, original Cdf = %lf \n",i,j,0,C[i][0][d]);
			}
#if 1
			else{
				for(v = 0; v < size[i]; v++){
					if(RTP_calculated(R[i][v]/frequency_scale[j],scale_function(i,v,d,frequency_scale[j])) < clone_seltable[i][j]){
//						ver[i][j]=v;
						clone_seltable[i][j] = RTP_calculated(R[i][v]/frequency_scale[j],scale_function(i,v,d,frequency_scale[j]));
//						if(clone_seltable[i][j]==0)
//							fprintf(stderr,"WTFFFFFFF task %d, version %d, core %d\n", i, v, j);
					}
					if(penalty_calculation(R[i][v]/frequency_scale[j],scale_function(i,v,d,frequency_scale[j])) < seltable[i][j]){
//						ver[i][j]=v;
						seltable[i][j] = penalty_calculation(R[i][v]/frequency_scale[j],scale_function(i,v,d,frequency_scale[j]));
//						if(seltable[i][j]==0)
//							fprintf(stderr,"WTFFFFFFF task %d, version %d, core %d\n", i, v, j);
					}
				}
			}
#endif
		}
	}
//  fprintf(stderr, "Table for MP before polution\n");
//  hungarian_print_matrix(seltable,X, delta);
	//till here, we will have a version selection table with the best versions
#endif

	return seltable;
}

struct core_resilience
{
  int taskNum;
  int core;
};
struct task_resilience
{
  int task;
  int core;
};
int compare_RTP(const void *a, const void *b){
	struct dtune_task* c = (struct dtune_task *)a;
	struct dtune_task* d = (struct dtune_task *)b;
	return (int)(d->RTP - c->RTP);
}
int compare_resi(const void *a, const void *b){
	struct task_resilience* c = (struct task_resilience *)a;
	struct task_resilience* d = (struct task_resilience *)b;
	return (int)(d->core - c->core);
}
int compareCoreResi(const void *a, const void *b){
	struct task_resilience* c = (struct task_resilience *)a;
	struct task_resilience* d = (struct task_resilience *)b;
	return (int)(c->core - d->core);
}
int** input_to_matrix(int rows, int cols){ //including version selection
	int i,j;
	int **pm;
	int **vs = version_selection(7); //with vs, the tasks only have single best version [task x delta];

	if(vs==NULL) return NULL;
	int start_core = 0, inc=1;
	if(delta == 3*rows){// all TMR
#if !dependency
		pm = (int**)calloc(rows,sizeof(int*));
		start_core= 2;
		inc = 3;
		ARBIT = 0;
//		fprintf(stderr, "TMR case, startcore index is %d\n",start_core);
#else
		start_core= 2;
		inc = 3;
		ARBIT = 0;
		struct task_resilience resi[X] = {};
		for(i=0;i<rows;i++){
			if(lambda[i] == 0){//NR, no need to sort
				resi[i].task = i;
				resi[i].core = -1;
			}else{
				resi[i].task = i;
				for(j=0;j<delta;j++){ //check s_i for each task
					if(vs[i][j] < 500000){ //by the order of cores
						resi[i].core += 1; //avaliable cores
					}
				}
			}
		}//now we have the list of core resilience and sort them with number of tasks.
		qsort(resi,X, sizeof(struct task_resilience), compareCoreResi);

		if(verbose){
			fprintf(stderr, "Resilence task :[");
			for(i=0;i<rows;i++)
				fprintf(stderr, "%d, ",resi[i].core);
			fprintf(stderr, "]\n");
			fprintf(stderr,"the lambda is: [");
			for(i=0;i<X;i++){
				fprintf(stderr,"%d, ",lambda[resi[i].task]);
			}
			fprintf(stderr,"]\n");
		}

		//we start the assignment from the core with the minimum number of tasks.
		int* assignedCore; //record of assignment
		assignedCore = (int*)calloc(delta, sizeof(int));
		int j;
		for(i=0;i<delta;i++)
			assignedCore[i]=0;

		for(i=0;i<X;i++){ //start from the task with the minimum number of tasks.
			if(lambda[resi[i].task]==1){//RMT tasks
				if(resi[i].core!=-1)
				{
					int count = 0;
					for(j=delta-1;j>=0&&count<3;j--){
						if(assignedCore[j]!=1&&vs[resi[i].task][j]<500000){
							assignedCore[j]=1;
							count++;
						}
					}
					if(count != 3){//it means that task[i] has no satisfication. due to the position overhead.
						return NULL;
					}
				}
			}
		}
		// Since the previous mapping alread checked whether it is feasible, the rest of steps build a dummy table for the routine.
		pm = (int**)calloc(rows,sizeof(int*)); //init the number of tasks

		for(i=0;i<rows;i++) //cores contain scale factor
		{
			int z=0;
			pm[i] = (int*)calloc(cols,sizeof(int));
			for(j=start_core;j<delta;j+=inc){
				pm[i][z]=0;
				z++;
			}
		}
		return pm;
#endif
	}else if(delta == rows){ //NR
		pm = (int**)calloc(rows,sizeof(int*));
		ARBIT = 0;
//		fprintf(stderr, "NR case \n");
		/*nothing to do*/
	}else{//arbitrary case
//		fprintf(stderr, "Arbitrary case\n");
		inc = 1;
		ARBIT = 1;

	/* Algorithm 2 exclude the TMR assigned cores from the selection version table "vs"
	 * and transform the table to NxN table for the rest of cores and tasks*/
		// we need a sorted list for TMR

		/*這邊用的trick是如果是沒有RMT task，就直接在外面就被Arbitrary flag撈掉了 -> 第一個一定是RMT task
		 *如果第一個的require core太小，576行，就return NULL
		 *如果第一個的require core大小合適，就把連同本身往前兩個index的core assign給這個task
		 *So on so forth*/
#if dependency
		struct task_resilience resi[X] = {};
		for(i=0;i<rows;i++){
			if(lambda[i] == 0){//NR, no need to sort
				resi[i].task = i;
				resi[i].core = -1;
			}else{
				resi[i].task = i;
				for(j=0;j<delta;j++){ //check s_i for each task
					if(vs[i][j] < 500000){ //by the order of cores
						resi[i].core += 1; //avaliable cores
					}
				}
			}
		}//now we have the list of core resilience and sort them with number of tasks.
		qsort(resi,X, sizeof(struct task_resilience), compareCoreResi);

		if(verbose){
			fprintf(stderr, "Resilence task :[");
			for(i=0;i<rows;i++)
				fprintf(stderr, "%d, ",resi[i].core);
			fprintf(stderr, "]\n");
			fprintf(stderr,"the lambda is: [");
			for(i=0;i<X;i++){
				fprintf(stderr,"%d, ",lambda[resi[i].task]);
			}
			fprintf(stderr,"]\n");
		}

		//we start the assignment from the core with the minimum number of tasks.
		int* assignedCore; //record of assignment
		assignedCore = (int*)calloc(delta, sizeof(int));
		int j;
		for(i=0;i<delta;i++)
			assignedCore[i]=0;

		for(i=0;i<X;i++){ //start from the task with the minimum number of tasks.
			if(lambda[resi[i].task]==1){//RMT tasks
				if(resi[i].core!=-1)
				{
					if(resi[i].core<3) return NULL;
					int count = 0;
					for(j=delta-1;j>=0&&count<3;j--){
						if(assignedCore[j]!=1&&vs[resi[i].task][j]<500000){
							assignedCore[j]=1;
							count++;
						}
					}
					if(count != 3){//it means that task[i] has no satisfication. due to the position overhead.
						return NULL;
					}
				}
			}
		}

		if(verbose){
			fprintf(stderr,"assigned core [");
			for(i=0;i<delta;i++)
			{
				fprintf(stderr,"%d ", assignedCore[i]);
			}
			fprintf(stderr,"]\n");
		}
#else
		struct task_resilience resi[X] = {};
		for(i=0;i<rows;i++){
			if(lambda[i] == 0){//NR, no need to sort
				resi[i].task = i;
				resi[i].core = -1;
			}else{
				resi[i].task = i;
				for(j=0;j<delta;j++){ //check s_i for each task
					if(vs[i][j] < 500000){ //by the order of cores
						resi[i].core = j;
					}
				}
			}
		}//now we have the list of resilience and sort them with the indexes
		qsort(resi,X, sizeof(struct task_resilience), compare_resi);
		if(verbose){
			fprintf(stderr,"list of resilience\n");
			for(i=0;i<rows;i++)
			{
				fprintf(stderr,"sorted task %d, core %d \n", resi[i].task, resi[i].core);
			}
		}
		int* assignedCore; //record of assignment
		assignedCore = (int*)calloc(delta, sizeof(int));
		int j;
		for(i=0;i<delta;i++)
			assignedCore[i]=0;
		if(resi[0].core < 2) //requirement is too tight
		{
			if(verbose)
				fprintf(stderr,"max resilience infeasible\n");
			return NULL;
		}
//		fprintf(stderr, "\n exclude task %d, core %d ", resi[0].task, resi[0].core);
		assignedCore[resi[0].core] = 1;
		assignedCore[resi[0].core-1] = 1;
		assignedCore[resi[0].core-2] = 1;
//		fprintf(stderr,"------------------%d\n", seltable[resi[0].task][resi[0].core-2]);

		int cur_c = resi[0].core-2; //current core is changed to index-2
		for(i=1;i<rows;i++)
		{
//			fprintf(stderr, "\n exclude task %d, core %d ", resi[i].task, resi[i].core);
			if(resi[i].core!=-1){
				if(resi[i].core < cur_c){ //表示當前剩下的core速度比要求的還要多
					if(resi[i].core < 2)
					{
						if(verbose)
						fprintf(stderr,"core A infeasible\n");
						return NULL;
					}
					assignedCore[resi[i].core] = 1;
					assignedCore[resi[i].core-1] = 1;
					assignedCore[resi[i].core-2] = 1;
					cur_c = resi[i].core-2;

				}else{//cur_c>resi_core 表示當前剩下的core速度比需求還要小，只能盡可能分配。
					if(cur_c < 3)
					{
						if(verbose)
						fprintf(stderr,"core B infeasible\n");
						return NULL;
					}
					assignedCore[cur_c-1] = 1;
					assignedCore[cur_c-2] = 1;
					assignedCore[cur_c-3] = 1;
					cur_c = cur_c-3;
				}
			}
		}//assigned list will contain the record of assigned cores.
		if(verbose){
			fprintf(stderr,"assigned core ");
			for(i=0;i<delta;i++)
			{
				fprintf(stderr,"%d ", assignedCore[i]);
			}
			fprintf(stderr,"\n");
		}
#endif
		// exclude the cores from vs to build a new table pm
		pm = (int**)calloc(n_nr,sizeof(int*)); //init the number of NR

		int o=0;
		for(i=0;i<rows;i++) //cores contain scale factor
		{
			if(lambda[i] == 1){//TMR
				continue;
			}
			pm[o] = (int*)calloc(n_nr,sizeof(int)); //generate the matrix of the rest of NR tasks for the HA.
			int z=0;
			for(j=0;j<delta;j+=1){
				if(assignedCore[j]!=1){
					pm[o][z]=vs[i][j]; //clone the best version information from vs table to pm matrix.
					z++;
				}
			}
			o++;
		}

		return pm; //only for arbitrary case
	}
	/* all NR or all TMR both cases are prepared here to solve by Algorithm1 with following graph pm[x*y]*/
	for(i=0;i<rows;i++) //cores contain scale factor
	{
		int z=0;
		pm[i] = (int*)calloc(cols,sizeof(int));
		for(j=start_core;j<delta;j+=inc){
			pm[i][z]=vs[i][j];
			z++;
		}
	}

	return pm;
}

int** array_to_matrix(int* m, int rows, int cols) {
  int i,j;
  int** r;
  r = (int**)calloc(rows,sizeof(int*));
  for(i=0;i<rows;i++)
  {
    r[i] = (int*)calloc(cols,sizeof(int));
    for(j=0;j<cols;j++)
      r[i][j] = m[i*cols+j];
  }
  return r;
}
void matrix_free(int** a, int rows, int cols){
	  int i,j;
	  for(i=0; i<rows; i++) {
		  for(j=0; j<cols; j++) {
			  a[i][j]=0;
		  }
		  free(a[i]);
	  }
	  free(a);
}
void input_datafree(double** a){
	  int i,j;
	  for(i=0; i<X; i++) {
		  for(j=0; j<size[i]; j++) {
			  a[i][j]=0;
		  }
		  free(a[i]);
	  }
	  free(a);
}
void version_datafree(double*** a, int deadline){
	  int i,j,t;
	  for(i=0; i<X; i++) {
		  for(j=0; j<size[i]; j++) {
			  for(t=0; t<deadline; t++) {
				  a[i][j][t]=0;
			  }
			  free(a[i][j]);
		  }
		  free(a[i]);
	  }
	  free(a);
}



int bruteForce(int* type, int tempDelta){//assume type is given

	int res=0, minReliability=999999;
	int a=0,b=0,c=0,d=0,e=0,f=0,g=0,i=0;
	int o=0;
	int* allocate_list;
	allocate_list = (int*)calloc(tempDelta,sizeof(int));
	int* min_allocate;
	min_allocate = (int*)calloc(tempDelta,sizeof(int));

//	fprintf(stderr,"the type is: [");
//	for(i=0;i<X;i++){
//		fprintf(stderr,"%d, ",type[i]);
//	}
//	fprintf(stderr,"]\n");
	for(a=0;a<tempDelta;a++){
		allocate_list[a]=-1;
		min_allocate[a]=-1;
	}
	int count=0, cor_ind;
	minReliability=999999;
	for(a=0;a<tempDelta;a++){
		res=0;
		int ao, as;
//		fprintf(stderr, "a = %d\n", a);
//		for(i=0;i<tempDelta;i++){
//			fprintf(stderr,"core %d allocate %d\n",i,allocate_list[i]);
//		}
		if(type[0]==0){
			res+=seltable[0][a];
//			fprintf(stderr,"seltable 0,a = %d\n", seltable[0][a]);
			allocate_list[a]=0;
		}else{
//			fprintf(stderr, "AAAAAAAAAAAAAAAAA\n");
			cor_ind=a;
			count=0;
			allocate_list[a]=0;
//			fprintf(stderr, "a = %d\n", a);
			for(o=1;o<tempDelta&&count!=2;o++){
				if(allocate_list[(a+o)%tempDelta]==-1){
					allocate_list[(a+o)%tempDelta]=0;
					if(count==0)
						ao = (a+o)%tempDelta;
					else
						as = (a+o)%tempDelta;
					count++;
					if((a+o)%tempDelta>cor_ind) cor_ind = (a+o)%tempDelta;
				}
			}
			res+=seltable[0][cor_ind];
//			for(i=0;i<tempDelta;i++){
//				fprintf(stderr,"By task A core %d allocate %d\n",i,allocate_list[i]);
//			}
		}
		for(b=0;b<tempDelta;b++){
			int bo, bs;
			if(allocate_list[b]==-1){
				if(type[1]==0){
					res+=seltable[1][b];
					allocate_list[b]=1;
				}else{
					cor_ind=b;
					count=0;
					allocate_list[b]=1;
					for(o=1;o<tempDelta&&count!=2;o++){
						if(allocate_list[(b+o)%tempDelta]==-1){
							allocate_list[(b+o)%tempDelta]=1;
							if(count==0)
								bo = (b+o)%tempDelta;
							else
								bs = (b+o)%tempDelta;
							count++;
							if((b+o)%tempDelta>cor_ind) cor_ind = (b+o)%tempDelta;
						}
					}
					res+=seltable[1][cor_ind];
				}
				for(c=0;c<tempDelta;c++){
					int co, cs;
					if(allocate_list[c]==-1){
						if(type[2]==0){
							res+=seltable[2][c];
							allocate_list[c]=2;
						}else{
							cor_ind=c;
							count=0;
							allocate_list[c]=2;
							for(o=1;o<tempDelta&&count!=2;o++){
								if(allocate_list[(c+o)%tempDelta]==-1){
									allocate_list[(c+o)%tempDelta]=2;
									if(count==0)
										co = (c+o)%tempDelta;
									else
										cs = (c+o)%tempDelta;
									count++;
									if((c+o)%tempDelta>cor_ind) cor_ind = (c+o)%tempDelta;
								}
							}
							res+=seltable[2][cor_ind];
						}
						for(d=0;d<tempDelta;d++){
							int d_o,ds;
							if(allocate_list[d]==-1){
								if(type[3]==0){
									res+=seltable[3][d];
									allocate_list[d]=3;
								}else{
									cor_ind=d;
									count=0;
									allocate_list[d]=3;
									for(o=1;o<tempDelta&&count!=2;o++){
										if(allocate_list[(d+o)%tempDelta]==-1){
											allocate_list[(d+o)%tempDelta]=3;
											if(count==0)
												d_o = (d+o)%tempDelta;
											else
												ds = (d+o)%tempDelta;
											count++;
											if((d+o)%tempDelta>cor_ind) cor_ind = (d+o)%tempDelta;
										}
									}
									res+=seltable[3][cor_ind];
								}
								for(e=0;e<tempDelta;e++){
									int eo, es;
									if(allocate_list[e]==-1){
										if(type[4]==0){
											res+=seltable[4][e];
											allocate_list[e]=4;
										}else{
											cor_ind=e;
											count=0;
											allocate_list[e]=4;
											for(o=1;o<tempDelta&&count!=2;o++){
												if(allocate_list[(e+o)%tempDelta]==-1){
													allocate_list[(e+o)%tempDelta]=4;
													if(count==0)
														eo = (e+o)%tempDelta;
													else
														es = (e+o)%tempDelta;
													count++;
													if((e+o)%tempDelta>cor_ind) cor_ind = (e+o)%tempDelta;
												}
											}
											res+=seltable[4][cor_ind];
										}
//										fprintf(stderr,"debuggggg\n");
//										for(i=0;i<tempDelta;i++){
//											fprintf(stderr,"By task B core %d allocate %d\n",i,allocate_list[i]);
//										}
										for(f=0;f<tempDelta;f++){
											int fo,fs;
											if(allocate_list[f]==-1){
												if(type[5]==0){
													res+=seltable[5][f];
													allocate_list[f]=5;
												}else{
													cor_ind=f;
													count=0;
													allocate_list[f]=5;
													for(o=1;o<tempDelta&&count!=2;o++){
														if(allocate_list[(f+o)%tempDelta]==-1){
															allocate_list[(f+o)%tempDelta]=5;
															if(count==0)
																fo = (f+o)%tempDelta;
															else
																fs = (f+o)%tempDelta;
															count++;
															if((f+o)%tempDelta>cor_ind) cor_ind = (f+o)%tempDelta;
														}
													}
													res+=seltable[5][cor_ind];
												}
												for(g=0;g<tempDelta;g++){
													int go,gs;
													if(allocate_list[g]==-1){
														if(type[6]==0){
															res+=seltable[6][g];
															allocate_list[g]=6;
														}else{
															cor_ind=g;
															count=0;
															allocate_list[g]=6;
															for(o=1;o<tempDelta&&count!=2;o++){
																if(allocate_list[(g+o)%tempDelta]==-1){
																	allocate_list[(g+o)%tempDelta]=6;
																	if(count==0)
																		go = (g+o)%tempDelta;
																	else
																		gs = (g+o)%tempDelta;
																	count++;
																	if((g+o)%tempDelta>cor_ind) cor_ind = (g+o)%tempDelta;
																}
															}
															res+=seltable[6][cor_ind];
														}
														if(0){
//															fprintf(stderr,"a=%d,b=%d,c=%d,d=%d,e=%d,f=%d,g=%d\n", a,b,c,d,e,f,g);
//															if(a==0)
//																fprintf(stderr,"AAAAAAAAAAAAAAAAAAA\n");
//															fprintf(stderr,"the type is: [");
//															for(i=0;i<X;i++){
//																fprintf(stderr,"%d, ",type[i]);
//															}
//															fprintf(stderr,"]\n");
															fprintf(stderr,"BBBBBBBBBBBB %d\n", res);
															fprintf(stderr,"the BBBBBBB mapping is: [");
															for(i=0;i<tempDelta;i++){
																fprintf(stderr,"%d, ",allocate_list[i]);
															}
															fprintf(stderr,"]\n");
															fprintf(stderr,"tempDelta %d, theBBBBBB mapping reliability is: [", tempDelta);
															for(i=0;i<tempDelta;i++){
																fprintf(stderr,"%d, ",seltable[allocate_list[i]][i]);
															}
															fprintf(stderr,"]\n");
														}
														if(res<0){
															fprintf(stderr,"**********DEBUGGGG********\n");
															fprintf(stderr,"BUG brute-force result %d\n", res);
															fprintf(stderr,"a=%d,b=%d,c=%d,d=%d,e=%d,f=%d,g=%d\n", a,b,c,d,e,f,g);
															fprintf(stderr,"the bug type is: [");
															for(i=0;i<X;i++){
																fprintf(stderr,"%d, ",type[i]);
															}
															fprintf(stderr,"]\n");
															fprintf(stderr,"tempDelta %d, the mapping is: [", tempDelta);
															for(i=0;i<tempDelta;i++){
//																fprintf(stderr,"%d, ",allocate_list[i]);
																fprintf(stderr,"%d, ",seltable[allocate_list[i]][i]);
															}
															fprintf(stderr,"]\n");
															return 0;
														}
														if(minReliability>res){
															minReliability = res;
															for(i=0;i<tempDelta;i++){
																min_allocate[i]=allocate_list[i];
															}
//															fprintf(stderr,"AAAAAAAAAA find the optimal %d\n", res);
//															fprintf(stderr,"the optimal mapping is: [");
//															for(i=0;i<tempDelta;i++){
//																fprintf(stderr,"%d, ",min_allocate[i]);
//															}
//															fprintf(stderr,"]\n");
//															fprintf(stderr,"tempDelta %d, the mapping reliability is: [", tempDelta);
//															for(i=0;i<tempDelta;i++){
//																fprintf(stderr,"%d, ",seltable[allocate_list[i]][i]);
//															}
//															fprintf(stderr,"]\n");
														}
														if(type[6]==0){
															allocate_list[g]=-1;
															res=res-seltable[6][g];
														}else{
															allocate_list[g]=-1;
															allocate_list[go]=-1;
															allocate_list[gs]=-1;
															res=res-seltable[6][cor_ind];
														}
													}
												}
												if(type[5]==0){
													allocate_list[f]=-1;
													res=res-seltable[5][f];
												}else{
													allocate_list[f]=-1;
													allocate_list[fo]=-1;
													allocate_list[fs]=-1;
													res=res-seltable[5][cor_ind];
												}
											}
										}
										if(type[4]==0){
											allocate_list[e]=-1;
											res=res-seltable[4][e];
										}else{
											allocate_list[e]=-1;
											allocate_list[eo]=-1;
											allocate_list[es]=-1;
											res=res-seltable[4][cor_ind];
										}
									}
								}
								if(type[3]==0){
									allocate_list[d]=-1;
									res=res-seltable[3][d];
								}else{
									allocate_list[d]=-1;
									allocate_list[d_o]=-1;
									allocate_list[ds]=-1;
									res=res-seltable[3][cor_ind];
								}
							}
						}
						if(type[2]==0){
							allocate_list[c]=-1;
							res=res-seltable[2][c];
						}else{
							allocate_list[c]=-1;
							allocate_list[co]=-1;
							allocate_list[cs]=-1;
							res=res-seltable[2][cor_ind];
						}
					}
				}
				if(type[1]==0){
					allocate_list[b]=-1;
					res=res-seltable[1][b];
				}else{
					allocate_list[b]=-1;
					allocate_list[bo]=-1;
					allocate_list[bs]=-1;
					res=res-seltable[1][cor_ind];
				}
			}

		}
		if(type[0]==0){
			allocate_list[a]=-1;
			res=res-seltable[0][a];
		}else{
			allocate_list[a]=-1;
			allocate_list[ao]=-1;
			allocate_list[as]=-1;
			res=res-seltable[0][cor_ind];
		}
	}
	if(1){
		fprintf(stderr,"***************suboptimal information***************\n");
		fprintf(stderr,"the type is: [");
		for(i=0;i<X;i++){
			fprintf(stderr,"%d, ",type[i]);
		}
		fprintf(stderr,"]\n");
		fprintf(stderr,"the optimal mapping is: [");
		for(i=0;i<tempDelta;i++){
			fprintf(stderr,"%d, ",min_allocate[i]);
		}
		fprintf(stderr,"]\n");
		fprintf(stderr,"the sub-optimal reliability = %d\n", minReliability);
		fprintf(stderr,"tempDelta %d, the mapping reliability is: [", tempDelta);
		for(i=0;i<tempDelta;i++){
			fprintf(stderr,"%d, ",seltable[min_allocate[i]][i]);
		}
		fprintf(stderr,"]\n");
		fprintf(stderr,"******************************\n");
	}
	fprintf(stderr,"*");
	free(min_allocate);
	free(allocate_list);
	return minReliability;
}


void seaInd(hungarian_problem_t* p, int** M){
	int i, j;
	int o=0, curRTP=-1, curInd=-1;
	if(0){
		hungarian_print_matrix(M,n_nr,n_nr);
		hungarian_print_matrix(p->assignment,n_nr,n_nr);
		hungarian_print_matrix(clone_seltable,X, delta);
//		hungarian_print_matrix(dtunetable,X, delta);
	}
	for(i=0;i<X;i++) //cores contain scale factor
	{
		if(lambda[i] != 1){//NR
			if(checkList[i]!=1){
				for(j=0;j<n_nr;j++){//找assignment
					if(p->assignment[o][j]==1){
						if(curRTP < M[o][j]){
							curRTP = M[o][j];
							curInd = i;
						}
					}
				}
			}//if checked, continue.
			o++;
		}
	}
	maxIndex = curInd;
	if(verbose)
		fprintf(stderr,"Maximal index is %d with penalty %d\n", curInd, curRTP);
}

int dtune(int rows, int cols){
	int i,j, objf=0;
	struct dtune_task a[X]={};
	for(i=0;i<X;i++){ //dTune排序的部分。
		int d = deadline[i];
#if referToFast
		a[i].RTP = ORTP_calculated(R[i][0],scale_function(i,0,d,1));
#else
		a[i].RTP = ORTP_calculated(R[i][0],scale_function(i,0,d,slowestFrequency));
#endif
		a[i].task = i;
	}

    qsort(a,X, sizeof(struct dtune_task), compare_RTP);
//    dtunetable = (int**)calloc(rows,sizeof(int*));
//	for(i=0;i<rows;i++)
//	{
//		dtunetable[i] = (int*)calloc(cols,sizeof(int));
//		for(j=0;j<cols;j++)
//			dtunetable[i][j]=0;
//	}
	//after sort.
	j=0;//index of core
	for(i=0;i<X;i++){
//		fprintf(stderr,"The RTP: %d, task %d, RTP in table %d, j=%d\n",a[i].RTP, a[i].task, clone_seltable[a[i].task][j], j);
		if(lambda[a[i].task]==0){//NR
			//fprintf(stderr, " ");
			objf += clone_seltable[a[i].task][j];
//			dtunetable[a[i].task][j]=1;
			j+=1;
		}else{//TMR
			objf += clone_seltable[a[i].task][j+2];
//			dtunetable[a[i].task][j]=1;
//			dtunetable[a[i].task][j+1]=1;
//			dtunetable[a[i].task][j+2]=1;
			j+=3;
		}
//		printf("j = %d \n", j);
	}
//	fprintf(stderr, "dTune result %d\n", objf);
	return objf;
}

double submain() {
	HA_result = 0; //really important
	hungarian_problem_t p;
	struct timespec start, end;
	clock_serv_t cclock;
	mach_timespec_t mts;
	double elapsedTime=0;

  /* an example cost matrix */
//  int r[5*4] =  {  10, 19, 8, 15,
//		   10, 18, 7, 17,
//		   13, 16, 9, 14,
//		   12, 19, 8, 18,
//		   14, 17, 10, 19 };

  int x = 7, y = 7;
  host_get_clock_service(mach_host_self(), CALENDAR_CLOCK, &cclock);
  clock_get_time(cclock, &mts);
  mach_port_deallocate(mach_task_self(), cclock);
  start.tv_sec = mts.tv_sec;
  start.tv_nsec = mts.tv_nsec;
  int** m = input_to_matrix(x, y); // m is the rest of tasks and cores in terms of DAC paper

  host_get_clock_service(mach_host_self(), CALENDAR_CLOCK, &cclock);
  clock_get_time(cclock, &mts);
  mach_port_deallocate(mach_task_self(), cclock);
  end.tv_sec = mts.tv_sec;
  end.tv_nsec = mts.tv_nsec;
  elapsedTime = dtime(start,end);
  microsec_sum+=elapsedTime;

  if(m == NULL){
	  if(verbose)
	  fprintf(stderr, "The input is not feasible!!\n");
	  version_datafree(C, 100);
	  version_datafree(P, 100);
	  version_datafree(SP,300);
	  return -1;
  }
//  fprintf(stderr,"HELLLLLLOOOOO");
#if 1
  /* initialize the hungarian_problem using the cost matrix*/
  int matrix_size = 0;

//  host_get_clock_service(mach_host_self(), CALENDAR_CLOCK, &cclock);
//  clock_get_time(cclock, &mts);
//  mach_port_deallocate(mach_task_self(), cclock);
//  start.tv_sec = mts.tv_sec;
//  start.tv_nsec = mts.tv_nsec;

  if(ARBIT == 0){
	  matrix_size = hungarian_init(&p, m , x,y, HUNGARIAN_MODE_MINIMIZE_COST);
//	  fprintf(stderr,"not arbitrary %dx%d\n", matrix_size,matrix_size);
  }
  else{ //for the rest of cores and tasks.
	  matrix_size = hungarian_init(&p, m , n_nr, n_nr, HUNGARIAN_MODE_MINIMIZE_COST);
//	  fprintf(stderr,"arbitrary %dx%d\n", matrix_size, matrix_size);
  }

  /* solve the assignement problem */
  hungarian_solve(&p);
  int MP_result = HA_result; //defined in hungarian.c as the total cost.

    host_get_clock_service(mach_host_self(), CALENDAR_CLOCK, &cclock);
    clock_get_time(cclock, &mts);
    mach_port_deallocate(mach_task_self(), cclock);
    end.tv_sec = mts.tv_sec;
    end.tv_nsec = mts.tv_nsec;
    elapsedTime = dtime(start,end);
    microsec_sum+=elapsedTime;

  /* timing output */
//  host_get_clock_service(mach_host_self(), CALENDAR_CLOCK, &cclock);
//  clock_get_time(cclock, &mts);
//  mach_port_deallocate(mach_task_self(), cclock);
//  start.tv_sec = mts.tv_sec;
//  start.tv_nsec = mts.tv_nsec;

//  fprintf(stderr, "Table for dTune\n");
//  hungarian_print_matrix(clone_seltable,X, delta);
  int dtune_result=dtune(X,delta);

//  host_get_clock_service(mach_host_self(), CALENDAR_CLOCK, &cclock);
//  clock_get_time(cclock, &mts);
//  mach_port_deallocate(mach_task_self(), cclock);
//  end.tv_sec = mts.tv_sec;
//  end.tv_nsec = mts.tv_nsec;
//  elapsedTime = dtime(start,end);
//  microsec_sum+=elapsedTime;

//  fprintf(stderr, "time %lf\n",elapsedTime);
//  if(max_sec < elapsedTime){
//
//	  max_sec = elapsedTime;
//	  fprintf(stderr, "MAX %lf\n",max_sec);
//  }
  /************/
  double res;
#if givenType
  res = (double)MP_result/dtune_result;
#else
  res = (double)MP_result;
  dTune_res=dtune_result;
//  if(BF_flag==0){
//	  BF_res=bruteForce(lambda);
//	  BF_flag = 1;
//  }
//  BF_res=bruteForce(lambda); //!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
//  fprintf(stderr, "MP is %d\n", MP_result);
//  fprintf(stderr, "dTune_result is %d\n", dtune_result);
//  fprintf(stderr, "Optimal res is %lf\n", res);
#endif
  if(MP_result>499999){
//	  fprintf(stderr, "MP is infeasible by violation %d\n", MP_result);
//	  hungarian_print_matrix(m,n_nr,n_nr);
//	  hungarian_print_matrix(p.assignment,n_nr,n_nr);
	  res = -1;
  }else if(MP_result >=0 && dtune_result >=0 && m != 0){
//	  fprintf(stderr, "%.f microseconds for dTune\n", elapsedTime);
	  //if there exist feasible solution, find the max Index
#if !givenType
//	  	  hungarian_print_matrix(m,n_nr,n_nr);
//	  	  hungarian_print_matrix(p.assignment,n_nr,n_nr);
	  seaInd(&p, m);
#endif

	  if(verbose){
		  fprintf(stderr, "************verbose************\n");
		  fprintf(stderr, "MP result Cost is %d\n",MP_result);
		  fprintf(stderr, "dtune_result %d\n", dtune_result);
		  fprintf(stderr, "Ratio : %lf \n", res);
		  fprintf(stderr, "Table for dTune\n");
		  hungarian_print_matrix(clone_seltable,X, delta);
//		  fprintf(stderr, "The dTune selection table:");
//		  hungarian_print_matrix(dtunetable,X, delta);
		  fprintf(stderr, "Table for MP\n");
		  hungarian_print_matrix(seltable,X, delta);
		  fprintf(stderr, "Core frequency scale:[");
		  int i;
		  for(i=0;i<delta;i++)
			  fprintf(stderr, "%lf, ", frequency_scale[i]);
		  fprintf(stderr, "]\n");
//		  if(seltable[5][1] == 0)
//		  fprintf(stderr, "!!!!!!!!!seltable value %d\n", seltable[5][1]);
//		  fprintf(stderr, "MP reduction\n");
		  hungarian_print_matrix(m,n_nr,n_nr);
		  fprintf(stderr, "Table for MP selection\n");
		  hungarian_print_assignment(&p);
		  if(res!=1)
			  fprintf(stderr,"HERE %lf, the ratio is not 1 \n", res);
		  fprintf(stderr,"***********\n");
	  }
  }else{
	  if(MP_result<0)
		  fprintf(stderr, "MP is infeasible ");
	  else if(dtune_result<0){
	  	  fprintf(stderr, "dtune is infeasible ");
	  	  fprintf(stderr, "Table for dTune\n");
	  	  hungarian_print_matrix(clone_seltable,X, delta);
	  }
//	  else if(MP_result/dtune_result >1)
//		  fprintf(stderr, "MP is not feasible, and dTune get the result\n");
	  res = -1;
  }

  /* free used memory */
  hungarian_free(&p);

  /*khchen free*/
  if(ARBIT == 0)
	  matrix_free(m, x, y);
  else
	  matrix_free(m, n_nr, n_nr);
  matrix_free(seltable, X, delta);
  matrix_free(clone_seltable, X, delta);//for dtune
//  matrix_free(dtunetable, X, delta);//for dtune


  input_datafree(R);
  input_datafree(AVG);

  version_datafree(C, 100);
  version_datafree(P, 100);
  version_datafree(SP,300);

#endif
  return res;
}
void generateArm(int d){

	srand(clock());

	//Shuffle the position of cores;
	int n = pow(X,2), val;
	while(n>1){
		n--;
		int k = rand()%n;
//		fprintf(stderr,"random k= %d\n", k);
		val = meshPosition[k];
		meshPosition[k]=meshPosition[n];
		meshPosition[n]=val;
	}
	//generate the frequencies of cores
	int j;
	for(j=0;j<d;j++){
			frequency_scale[j]=1-(j%4)*W;
	}
	qsort(frequency_scale,d,sizeof(frequency_scale[0]),compare_frequency);
}


void generateMesh(){

	srand(clock());

	//Shuffle the position of cores;
	int n = pow(X,2), val;
	while(n>1){
		n--;
		int k = rand()%n;
//		fprintf(stderr,"random k= %d\n", k);
		val = meshPosition[k];
		meshPosition[k]=meshPosition[n];
		meshPosition[n]=val;
	}
	//generate the frequencies of cores
	int j;
	for(j=0;j<49;j++){
	#if constant
		#if speed_level
			frequency_scale[j]=1-(j%4)*W;
		#endif
	#else
		#if normal_dis
			//normal distribution
			frequency_scale[j]=norm(1-W,SD);
	//		fprintf(stderr,"original %lf \n",frequency_scale[j]);
		#else
			//uniform random variable
			frequency_scale[j]=1-((double)rand()/(RAND_MAX))*W;
	//		fprintf(stderr,"original %lf ",frequency_scale[j]);
	#endif
	//	fprintf(stderr, "\n");
	//	for(j=0;j<delta;j++)
	//		fprintf(stderr,"sorted %lf ",frequency_scale[j]);
	#endif
	}
#if !constant
	qsort(frequency_scale,49,sizeof(frequency_scale[0]),compare_frequency);
#endif
}
int main(){

	double sub_result;
	int i;
	int z; // z is the variations
	max_sec = 0.0;
	SD = 0.05;
	frequency_scale = (double*)calloc(49,sizeof(double)); //prepare a 2D-mash
	for(i=0;i<49;i++)
		frequency_scale[i]=-1;
	/*generate the information of cores*/

#if	givenType
#if constant
	for(z=0;z<=10;z++){
		generateMesh();
		int count = 128;
		sub_result = 0;
		W=0.1+(0.02*z);

		/*constant test*/
//		W=0.1;z=10;
		microsec_sum=0.0;
		for(i=0;i<128;i++){ //automation simulation
			protection_generate(i); //lambda determination
			qsort(frequency_scale,delta,sizeof(frequency_scale[0]),compare_frequency);
//			for(k=0;k<delta;k++)
//				fprintf(stderr,"frequency scale %lf\n", frequency_scale[k]);
//			fprintf(stderr,"************\n");
			  if(verbose)
				  fprintf(stderr,"Protection type is %d\n", i);
			  double r = (double)submain();
			  if(r>1){
//				  fprintf(stderr,"error result %lf\n", r);
				  sub_result+=1;
			  }
			  else if(r >= 0){
				  sub_result+=r;
			  }else{//infeasible
//			  	fprintf(stderr,"infesible result %lf\n", r);
				  count -=1;
			  }

		}
		/*feasible count*/
//		fprintf(stderr,"count %d\n", count);
		/*time of ms*/
//		fprintf(stderr, "%.f\n", (double)microsec_sum/128);
		/*result*/
		fprintf(stderr,"%lf \n",sub_result/count);
	}
//	fprintf(stderr, "%.f\n", (double)max_sec);
#else
	int j;
	double random_result=0.0;
#if normal_dis
	for(z=0;z<=10;z++){
		random_result=0.0;
		W = 0.1+(0.02*z);
		double nor_ms_sum = 0.0;

		for(j=0;j<1;j++){
			generateMesh();

			int count = 128;
			sub_result=0;
			microsec_sum=0.0;
			for(i=0;i<128;i++){ //automation simulation
			  protection_generate(i);
			  double r = (double)submain();
			  if(r>1){
//				  fprintf(stderr,"error result %lf\n", r);
				  sub_result+=1;
			  }
			  else if(r >= 0){
				  sub_result+=r;
			  }else{//infeasible
//  			  	fprintf(stderr,"infesible result %lf\n", r);
				  count -=1;
			  }
			}
//			fprintf(stderr, "subresult %lf \n", sub_result/31);
//			if(count <=20)
//			fprintf(stderr,"count %d\n", count);
			random_result+=(sub_result/count);
//			random_result+=(sub_result);
	//		fprintf(stderr, "subresult %lf ", sub_result/31);
			nor_ms_sum += microsec_sum/128;

		}
//		fprintf(stderr, "%.f\n", (double)nor_ms_sum/50);
		fprintf(stderr,"%lf \n",random_result);
	}
#else
	//uniform distribution
//	for(z=0;z<=10;z++){
	z=0;
		random_result=0.0;
		W=0.1+(0.02*z);
		double nor_ms_sum = 0.0;
//		fprintf(stderr,"%lf", W);
		for(j=0;j<1;j++){
			generateMesh();
			microsec_sum=0.0;
			int count = 128;
			sub_result=0;
			for(i=0;i<128;i++){ //automation simulation
//			  fprintf(stderr,"protection %d\n", i);
			  protection_generate(i);
			  double r = (double)submain();
//			  fprintf(stderr,"result %lf\n", r);
			  if(r>1){
//				  fprintf(stderr,"error result %lf\n", r);
				  sub_result+=1;
			  }
			  else if(r >= 0){
				  sub_result+=r;
			  }else{//infeasible
//				  	fprintf(stderr,"infesible result %lf\n", r);
				  count -=1;
			  }
			  if(count == 0)
			  fprintf(stderr,"count %d\n", count);
			}
			fprintf(stderr,"count %d\n", count);
	//		fprintf(stderr, "subresult %lf ", sub_result);
			random_result+=(sub_result/count);
			nor_ms_sum += microsec_sum/128;
		}
//		fprintf(stderr, "%.f\n", (double)nor_ms_sum/50); //time
		fprintf(stderr,"%lf \n",random_result/1);
//	}
	#endif
#endif
#else
#if constant
	int H=0; //default = 1
	generateMesh();
	for(H=0;H!=Y+1;H++){
//	for(z=0;z<=10;z++){ //10次的variations
	z=2;

			int loopCount = H;
			int curType=-1;
			int tempLambda[X];
			sub_result = 0;
			W=0.1+(0.02*z);
			microsec_sum=0.0;
			maxIndex=-1;
			for(i=0;i<X;i++){ //init the checklist{
				checkList[i]=0;
				tempLambda[i]=0;
//				fprintf(stderr,"checklist update\n");
			}
			if(verbose){
				fprintf(stderr,"*********************\n");
				fprintf(stderr,"z = %d\n", z);
			}
			int curExecutionType = 0;

			BF_flag=1;
			/*brute-force section*/
			if(BF_flag == 0){
				BF_flag+=1;
				int a,b,c,d,e,f;
				int optimalReliability=9999999;
				if(H==7){
					for(i=0;i<X;i++){
						tempLambda[i]=1;
					}
				}else{
				for(a=0;a<7&&H>0;a++){
					if(tempLambda[a]!=1){
						tempLambda[a]=1;
						for(b=0;b<7&&H>1;b++){
							if(tempLambda[b]!=1){
								tempLambda[b]=1;
								for(c=0;c<7&&H>2;c++){
									if(tempLambda[c]!=1){
										tempLambda[c]=1;
										for(d=0;d<7&&H>3;d++){
											if(tempLambda[d]!=1){
												tempLambda[d]=1;
												for(e=0;e<7&&H>4;e++){
													if(tempLambda[e]!=1){
														tempLambda[e]=1;
														for(f=0;f<7&&H>5;f++){
															if(tempLambda[f]!=1){
																tempLambda[f]=1;
																if(H==6){
																	bruteVersion(calculateTempDelta(tempLambda),tempLambda);
																	int curRes=bruteForce(tempLambda, calculateTempDelta(tempLambda));
																	if(curRes<optimalReliability&&curRes!=-1)
																		optimalReliability=curRes; // start from 0;
																}
																tempLambda[f]=0;
															}
														}
														if(H==5){
															bruteVersion(calculateTempDelta(tempLambda),tempLambda);
															int curRes=bruteForce(tempLambda, calculateTempDelta(tempLambda));
															if(curRes<optimalReliability&&curRes!=-1)
																optimalReliability=curRes; // start from 0;
														}
														tempLambda[e]=0;
													}
												}
												if(H==4){
													bruteVersion(calculateTempDelta(tempLambda),tempLambda);
													int curRes=bruteForce(tempLambda, calculateTempDelta(tempLambda));
													if(curRes<optimalReliability&&curRes!=-1)
														optimalReliability=curRes; // start from 0;
												}
												tempLambda[d]=0;
											}
										}
										if(H==3){
											bruteVersion(calculateTempDelta(tempLambda),tempLambda);
											int curRes=bruteForce(tempLambda, calculateTempDelta(tempLambda));
											if(curRes<optimalReliability&&curRes!=-1)
												optimalReliability=curRes; // start from 0;
										}
										tempLambda[c]=0;
									}
								}
								if(H==2){
									bruteVersion(calculateTempDelta(tempLambda),tempLambda);
									int curRes=bruteForce(tempLambda, calculateTempDelta(tempLambda));
									if(curRes<optimalReliability&&curRes!=-1)
										optimalReliability=curRes; // start from 0;
								}
								tempLambda[b]=0;
							}
						}
						if(H==1){
							bruteVersion(calculateTempDelta(tempLambda),tempLambda);
							int curRes=bruteForce(tempLambda, calculateTempDelta(tempLambda));
							if(curRes<optimalReliability&&curRes!=-1)
								optimalReliability=curRes; // start from 0;
						}
						tempLambda[a]=0; //reset
					}
				}
				}
				if(H==0||H==7){
					bruteVersion(calculateTempDelta(tempLambda),tempLambda);
					int curRes=bruteForce(tempLambda, calculateTempDelta(tempLambda));
					if(curRes<optimalReliability&&curRes!=-1)
						optimalReliability=curRes; // start from 0;
				}
				fprintf(stderr,"\nthe optimal reliability %d\n", optimalReliability);



				//free the memory allocation
				matrix_free(seltable, X, calculateTempDelta(tempLambda));
				matrix_free(clone_seltable, X, calculateTempDelta(tempLambda));//for dtune
				input_datafree(R);
				input_datafree(AVG);
				version_datafree(C, 100);
				version_datafree(P, 100);
				version_datafree(SP,300);
			}
			if(H==7){
				protection_generate(127);
			}else{
				protection_generate(0); //自帶delta計算。
			}
			if(H==0)
				qsort(frequency_scale,9,sizeof(frequency_scale[0]),compare_frequency); //trick for 5% set delta ->9
			else
				qsort(frequency_scale,delta,sizeof(frequency_scale[0]),compare_frequency);
			double r = (double)submain(); //first mapping
			if(0){
				fprintf(stderr,"the init max Index %d\n", maxIndex);
				fprintf(stderr,"initR = %lf \n",r);
			}
			if(r == -1){
				if(verbose)
				fprintf(stderr,"No feasible solution in first round \n");
			}else if(maxIndex==-1){
				if(verbose)
				fprintf(stderr,"No index in first round \n");
			}else{
				//is feasible then:
				sub_result=r;
				checkList[maxIndex]=1;
				curType = exchange[maxIndex];
				curExecutionType += curType;
				protection_generate(curExecutionType);
				//在這邊core的數量是一開始就定好的，即loopCount是鎖定成Y。Y=7~1 3Y+X-Y是core的總數
				//做完每次的mapping後，找到最大reliability penalty的task 把protection type設1
				//checkList[i]=0 表示task i還沒測試過。 測過改成1 然後loopCount-1
				//最大的penalty task index會記在global變數maxIndex
				//maxIndex在找的時候，如果checkList已經為1 表示找過了。
				//總共只要mapping7次(task數)基本上。
				while(loopCount>0){ //表示core還有剩
					if(verbose){
						fprintf(stderr,"Count of non-considered task %d\n", loopCount);
						fprintf(stderr,"Protection type is %d\n", curExecutionType);
					}
					protection_generate(curExecutionType);
					maxIndex = -1;
					r = (double)submain();
					if(verbose)
						fprintf(stderr,"the max Index %d\n", maxIndex);
					if(maxIndex == -1){//no checking->rollback but checklist is already 1;
						curExecutionType -= curType;
						if(curExecutionType<0)
							fprintf(stderr,"Rollback BUGGGGGGGGGG \n");
					}else{
						checkList[maxIndex]=1; //check next index
						curType = exchange[maxIndex];
						curExecutionType += curType;
						loopCount-=1;
						if(r>=0){
							sub_result=r;
							if(verbose)
								fprintf(stderr,"Normal R = %lf \n",r);
							//next loop
						}else if(r>1){
							sub_result=r;
							if(verbose)
								fprintf(stderr,"BIG PROBLEM R = %lf \n",r);
						}else{
							if(verbose)
								fprintf(stderr,"there is no fesible mapping %lf\n", r);
						}
					}

				}//算完後 輸出當下的r就好。(ratio)
//				fprintf(stderr,"%d \n",BF_res);
				fprintf(stderr,"%lf \n",sub_result/dTune_res);
//				fprintf(stderr,"%d \n",dTune_res);
//				fprintf(stderr,"********************\n");
			}
	}//H
#else
	int j;
	double random_result=0.0, random_dTune=0.0;
	int H=0;
	for(;H!=Y;H++){
//		BF_flag=0;
//	for(z=0;z<=10;z++){ //10次的variations
		z=2;
		random_result=0.0, random_dTune=0.0;
		W = 0.1+(0.02*z);
		double nor_ms_sum = 0.0;
//		for(j=0;j<1;j++){
			generateMesh();
			int loopCount = H;
			int curType=-1;
			int tempLambda[X]={};
			sub_result = 0;
			W=0.1+(0.02*z);
			microsec_sum=0.0;
			maxIndex=-1;
			for(i=0;i<X;i++){ //init the checklist{
				checkList[i]=0;
				tempLambda[i]=0;
	//				fprintf(stderr,"checklist update\n");
			}
			if(0){
				fprintf(stderr,"*********************\n");
				fprintf(stderr,"z = %d\n", z);
			}
			int curExecutionType = 0;
			if(H==7){
				protection_generate(127);
			}else{
				protection_generate(0); //自帶delta計算。
			}

			/*brute-force section*/
			BF_flag=1;
			if(BF_flag == 0){
				BF_flag+=1;
				int a,b,c,d,e,f;
				int optimalReliability=9999999;
				if(H==7){
					for(i=0;i<X;i++){
						tempLambda[i]=1;
					}
				}else{
				for(a=0;a<7&&H>0;a++){
					if(tempLambda[a]!=1){
						tempLambda[a]=1;
						for(b=0;b<7&&H>1;b++){
							if(tempLambda[b]!=1){
								tempLambda[b]=1;
								for(c=0;c<7&&H>2;c++){
									if(tempLambda[c]!=1){
										tempLambda[c]=1;
										for(d=0;d<7&&H>3;d++){
											if(tempLambda[d]!=1){
												tempLambda[d]=1;
												for(e=0;e<7&&H>4;e++){
													if(tempLambda[e]!=1){
														tempLambda[e]=1;
														for(f=0;f<7&&H>5;f++){
															if(tempLambda[f]!=1){
																tempLambda[f]=1;
																if(H==6){
																	bruteVersion(calculateTempDelta(tempLambda),tempLambda);
																	int curRes=bruteForce(tempLambda, calculateTempDelta(tempLambda));
																	if(curRes<optimalReliability&&curRes!=-1)
																		optimalReliability=curRes; // start from 0;
																}
																tempLambda[f]=0;
															}
														}
														if(H==5){
															bruteVersion(calculateTempDelta(tempLambda),tempLambda);
															int curRes=bruteForce(tempLambda, calculateTempDelta(tempLambda));
															if(curRes<optimalReliability&&curRes!=-1)
																optimalReliability=curRes; // start from 0;
														}
														tempLambda[e]=0;
													}
												}
												if(H==4){
													bruteVersion(calculateTempDelta(tempLambda),tempLambda);
													int curRes=bruteForce(tempLambda, calculateTempDelta(tempLambda));
													if(curRes<optimalReliability&&curRes!=-1)
														optimalReliability=curRes; // start from 0;
												}
												tempLambda[d]=0;
											}
										}
										if(H==3){
											bruteVersion(calculateTempDelta(tempLambda),tempLambda);
											int curRes=bruteForce(tempLambda, calculateTempDelta(tempLambda));
											if(curRes<optimalReliability&&curRes!=-1)
												optimalReliability=curRes; // start from 0;
										}
										tempLambda[c]=0;
									}
								}
								if(H==2){
									bruteVersion(calculateTempDelta(tempLambda),tempLambda);
									int curRes=bruteForce(tempLambda, calculateTempDelta(tempLambda));
									if(curRes<optimalReliability&&curRes!=-1)
										optimalReliability=curRes; // start from 0;
								}
								tempLambda[b]=0;
							}
						}
						if(H==1){
							bruteVersion(calculateTempDelta(tempLambda),tempLambda);
							int curRes=bruteForce(tempLambda, calculateTempDelta(tempLambda));
							if(curRes<optimalReliability&&curRes!=-1)
								optimalReliability=curRes; // start from 0;
						}
						tempLambda[a]=0; //reset
					}
				}
				}
				if(H==0||H==7){
					bruteVersion(calculateTempDelta(tempLambda),tempLambda);
					int curRes=bruteForce(tempLambda, calculateTempDelta(tempLambda));
					if(curRes<optimalReliability&&curRes!=-1)
						optimalReliability=curRes; // start from 0;
				}
				fprintf(stderr,"\nthe optimal reliability %d\n", optimalReliability);



				//free the memory allocation
				matrix_free(seltable, X, calculateTempDelta(tempLambda));
				matrix_free(clone_seltable, X, calculateTempDelta(tempLambda));//for dtune
				input_datafree(R);
				input_datafree(AVG);
				version_datafree(C, 100);
				version_datafree(P, 100);
				version_datafree(SP,300);
			}

		    double r = (double)submain(); //first mapping
			if(0){
				fprintf(stderr,"the init max Index %d\n", maxIndex);
				fprintf(stderr,"initR = %lf \n",r);
			}
			if(r == -1){
				if(verbose)
				fprintf(stderr,"No feasible solution in first round \n");
			}else if(maxIndex==-1){
				if(verbose)
				fprintf(stderr,"No index in first round \n");
			}else{
				//is feasible then:
				sub_result=r;
				checkList[maxIndex]=1;
				curType = exchange[maxIndex];
				curExecutionType += curType;
				//在這邊core的數量是一開始就定好的，即loopCount是鎖定成Y。Y=7~1 3Y+X-Y是core的總數
				//做完每次的mapping後，找到最大reliability penalty的task 把protection type設1
				//checkList[i]=0 表示task i還沒測試過。 測過改成1 然後loopCount-1
				//最大的penalty task index會記在global變數maxIndex
				//maxIndex在找的時候，如果checkList已經為1 表示找過了。
				//總共只要mapping7次(task數)基本上。
				while(loopCount>0&&loopCount<6){ //表示core還有剩
//					int k, test=0;
//					for(k=0;k<X;k++){
//						fprintf(stderr,"check list task %d = %d\n",k, checkList[k]);
//						if(checkList[k]==1)
//							test+=1;
//					}
//					for(k=0;k<49;k++){
//						fprintf(stderr,"Type %d = %d\n",k, lambda[k]);
//						fprintf(stderr,"%lf\n",frequency_scale[k]);
//					}
					if(verbose){
						fprintf(stderr,"********loop********\n");
						fprintf(stderr,"Count of non-considered task %d\n", loopCount);
						fprintf(stderr,"Protection type is %d\n", curExecutionType);

					}
					protection_generate(curExecutionType);
					maxIndex = -1;
					r = (double)submain();
					if(verbose){
						fprintf(stderr,"the max Index %d\n", maxIndex);
					}
					if(maxIndex == -1){//no checking->rollback but checklist is already 1;
						curExecutionType -= curType;
						if(curExecutionType<0){
							fprintf(stderr,"Rollback BUGGGGGGGGGG \n");
							fprintf(stderr,"no Index R = %lf \n",r);

							if(curExecutionType<-2) {
								return 0;
							}
						}
					}else{
						checkList[maxIndex]=1; //check next index
						curType = exchange[maxIndex];
						curExecutionType += curType;
						loopCount-=1;
						if(r>=0){
							sub_result=r;
							if(verbose)
							fprintf(stderr,"Normal R = %lf \n",r);
							//next loop
						}else if(r>1){
							sub_result=r;
							if(verbose)
							fprintf(stderr,"BIG PROBLEM R = %lf \n",r);
						}else{
							if(verbose)
							fprintf(stderr,"there is no fesible mapping %lf\n", r);
						}
					}

				}//算完後 輸出當下的r就好。(ratio)
				if(verbose)
					fprintf(stderr,"final %lf \n",sub_result);
				random_result+=sub_result;
				random_dTune+=dTune_res;
				nor_ms_sum += microsec_sum/Y;
			}
//		}
		fprintf(stderr,"%lf \n",random_result/random_dTune);
//		fprintf(stderr,"%lf \n",random_dTune/1);
//		fprintf(stderr,"********************\n");
//		BF_flag=0;
//	}//Z
	}//H
#endif
#endif
	return 0;
}

