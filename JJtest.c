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
 ********************************************************************/


#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "hungarian.h"
#define INF (0x7FFFFFFF)
#define X 5

int lambda[X]={0,0,0,0,0}; //five tasks,1 = TMR, 0=NR
int size[X]={4,24,1,2,5}; //version size
int deadline[X]={50,30,18,25,60}; //version size
float alpha = 0.5;
int alphascale = 1000; //without scale
int Rscale = 1000; //10^-6
int delta=0, lamd=0;
int pro_order[X]={};

int **seltable, **dtunetable, **final_assignment;
double **R, **AVG, ***C, ***P, ***SP;

int RTP_calculated(double R, double C){
	double RTP = (alpha/alphascale)*R+(1-alpha)*(1-C);
//	printf("1-C %lf \n", (1-C));
	int RTPscale = 1000000;
//	int RTPscale = 1000;
//	printf("TEETETETET %lf \n", RTP);
	return (int)(RTP*RTPscale);
}
double scale_function(int func, int version, int deadline, int core, double scale){
	int t=0;
	double res = 0, sum = 0;
//	printf("scale func %d version %d deadline %d on core %d to scale %lf\n", func, version, deadline, core, scale);
	for(t=0;t<=300;t++){//init SPtable
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
	for(t=0;t<=deadline;t++){
		if(SP[func][version][t]!=0){
			res+=SP[func][version][t];
//			printf("SP[%d]=%lf \n",t, SP[func][version][t]);
		}
	}
//	printf("Origin result = %lf \n",C[func][version][deadline]);
//	printf("New result = %lf \n",res);
	return res;
}

int** version_selection(int rows, int cols){
	int i, j, v;
	int **ver;

	srand(1);
	//delta is the demand cores of all tasks
	delta = X;
	fprintf(stderr,"lambda :\n");
	for(i=0;i<X;i++){
		if(lambda[i] == 1){
			delta +=2;
			lamd++;
		}
		fprintf(stderr,"task %d = %d ", i, lambda[i]);
	}
	fprintf(stderr,"Delta = %d\n", delta);
	// include the speed of cores information
	double *frequency_scale = (double*)calloc(delta,sizeof(double));
	for(j=0;j<delta;j++){
//		frequency_scale[j]=1-0.2-(0.025*j);
		frequency_scale[j]=1-0.2-rand()*1.0/RAND_MAX*0.5;
	}
	R = (double**)calloc(rows,sizeof(double*));
	for(i=0;i<rows;i++){ //for each task
		R[i]=(double*)calloc(size[i],sizeof(double));
	}
	AVG = (double**)calloc(rows,sizeof(double*));
	for(i=0;i<rows;i++){ //for each task
		AVG[i]=(double*)calloc(size[i],sizeof(double));
	}
	//read input part
	//strcpy(str1,"PAInput/Rij.txt");
	FILE *file = fopen("PAInput/Rij.txt", "r");
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
		//printf("%lf\n", R[iInd][jInd]);
		//printf("%lf\n", AVG[iInd][jInd]);
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
			SP[i][v]=(double*)calloc(300,sizeof(double));
		}
	}

	char str2[80];
	char str3[5];
	int eSample=0,t;
	double cValue, cValueOld =0;
	for(i=0;i<rows;i++){ //for each task
		for(v = 0; v < size[i]; v++){
//			printf("version %d\n",v);
			strcpy(str2,"PAInput/");
			str3[0]=48+i;
			strcat(str2, str3); strcat(str2, "/");
			if((v/10)!=0){
				str3[0]=(48+v/10);
				strcat(str2, str3);
			}
			str3[0]=(48+v%10);
			strcat(str2, str3);strcat(str2, ".txt");
			if(i!=1){ //read file
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
						for(;t<(int)(eSample/100000.0)&& t<=100; t++){
							C[i][v][t]=cValueOld;
						}
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
					if(t>=(int)(AVG[i][v]/100000.0))
						C[i][v][t]=1;
					else
						C[i][v][t]=0;
				}
			}
		}
	}
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
//		printf("function %d", i);
//		for(v=0;v<size[i];v++){
//			printf("version %d", v);
//			for(t=0;t<100;t++)
//				printf("%lf \n", C[i][v][t]);
//		}
//	}
//	printf("%d",RTP_calculated(R[0][0],C[0][0][deadline[100]]));

	//it is important to change the CDF for each core beforehand


	// version seletcion part

	seltable = (int**)calloc(rows,sizeof(int*));
	ver = (int**)calloc(rows,sizeof(int*));
#if 1
	for(i=0;i<rows;i++) //for each task
	{
		seltable[i] = (int*)calloc(delta,sizeof(int));
		ver[i] = (int*)calloc(delta,sizeof(int));
		int d = deadline[i];

		for(j=0;j<delta;j++){// for each cores

			if(lambda[i] == 1){
				ver[i][j]=0;//highest performance version
//				printf(("R = %lf \n"),R[i][0]);
//				printf(("%lf \n"),C[i][0][d]);
				seltable[i][j] = RTP_calculated(0,scale_function(i,0,d,j,frequency_scale[j]));//RTP
//				printf(("RTP = %d \n"),seltable[i][j]);
//				printf(("Function %d, core %d, version %d, original Cdf = %lf \n"),i,j,0,C[i][0][d]);
			}
#if 1
			else{
				seltable[i][j] = INF;
				for(v = 0; v < size[i]; v++){
					if(RTP_calculated(R[i][v]/frequency_scale[j],scale_function(i,v,d,j,frequency_scale[j])) < seltable[i][j]){
						ver[i][j]=v;
						seltable[i][j] = RTP_calculated(R[i][v]/frequency_scale[j],scale_function(i,v,d,j,frequency_scale[j]));
					}
				}

			}
#endif
		}

	}

#if 0
	for(i=0;i<rows;i++) //cores contain scale factor
	{
		for(j=0;j<delta;j++){ // functions
			fprintf(stderr,"function %d best version on core %d RTP %d \n",i, j, seltable[i][j]);
		}
	}
#endif
#endif

	return seltable;
}



int** input_to_matrix(int rows, int cols){ //including version selection
	int i,j;
	int **pm;
	int **vs = version_selection(5,5); //with vs, the tasks only have single version
	int start_core = 0, inc=1;
	if(delta == 3*rows){// all TMR
		start_core= 2;
		inc = 3;
		printf("TMR case, startcore index is %d\n",start_core);
	}else if(delta == rows){ //NR
		printf("NR case \n");
		/*nothing to do*/
	}else{//arbitrary case
		start_core = lamd*2;
		inc = 1;
		printf("Arbitrary case, startcore index is %d\n",start_core);
	}
#if 0
	for(i=0;i<rows;i++){
		for(j=start_core;j<delta;j+=inc){
			fprintf(stderr,"%d \n", seltable[i][j]);
		}
	}
#endif

//	printf("%d ", vs[0][0]);printf("%d ", vs[0][1]);
//	printf("%d ", vs[1][1]);
	//

	/* Promoting Algorithm here.
	 * Here Rows = number of rows, Cols = number of cols
	 * We first do the preprocess of input transformation for version selection.
	 * In the version selection,the best versions of tasks on each core will be recorded in array.
	 * And assign the best versions RTP to matrix r and return the matrix.
	 * */
#if 0
	return vs;
#else
	/*Assign the graph matrix R with the best versions*/
	pm = (int**)calloc(rows,sizeof(int*));
		for(i=0;i<rows;i++) //cores contain scale factor
		{
			int z=0;
			pm[i] = (int*)calloc(cols,sizeof(int));
			for(j=start_core;j<delta;j+=inc){
//				printf("function %d on core %d RTP %d\n", i, j, vs[i][j]);
				pm[i][z]=vs[i][j];
				z++;
			}
		}
#endif
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
int promoting_sequence(int** A, int** C, int rows, int cols){
	int i,j,z=0, objf=0;

	//promoting order construction
#if 1
	for(i=0; i<rows; i++){
		for(j=0; j<cols; j++) {
			if(A[j][i] == 1){
				pro_order[z++]=j;
			}
		}
	}
#else
	for(i=0; i<rows; i++){
		for(j=0; j<cols; j++) {
			if(A[j][i] == 1 && lambda[j]==0){
				pro_order[z++]=j;
			}
		}
	}
	for(i=0; i<rows; i++){
		for(j=0; j<cols; j++) {
			if(A[j][i] == 1 && lambda[j]==1){
				pro_order[z++]=j;
			}
		}
	}
#endif


	final_assignment = (int**)calloc(rows,sizeof(int*));
	for(i=0;i<rows;i++)
	{
		final_assignment[i] = (int*)calloc(delta,sizeof(int));
	   	for(j=0;j<delta;j++)
	   		final_assignment[i][j]=0;
	}

	//after the order is prepared.
	j=0;//index of core
	for(i=0;i<rows;i++){
//		fprintf(stderr, "task %d ", pro_order[i]);
		if(lambda[pro_order[i]]==0){//NR
//			fprintf(stderr, "NR task %d \n", pro_order[i]);
			objf += seltable[pro_order[i]][j];
			final_assignment[pro_order[i]][j]=1;
			j++;
		}else{//TMR
//			fprintf(stderr, "TMR task %d \n", pro_order[i]);
			objf += seltable[pro_order[i]][j+2];
			final_assignment[pro_order[i]][j]=1;
			final_assignment[pro_order[i]][j+1]=1;
			final_assignment[pro_order[i]][j+2]=1;
			j+=3;
		}
//		printf("j = %d \n", j);
	}
	return objf;
}

struct dtune_task
{
  int task;
  int RTP;
};
int compare_RTP(const struct dtune_task *a, const struct dtune_task *b){
	return b->RTP - a->RTP;
}
int dtune(int rows, int cols){
	int i,j, objf=0;
	struct dtune_task a[X]={};
	for(i=0;i<X;i++){
		a[i].RTP = seltable[i][0];
		a[i].task = i;
	}



	//arr contain the RTP;
//	printf("The original RTP: %d, task %d ",a[0].RTP, a[0].task);
	qsort(a,X, sizeof(struct dtune_task), compare_RTP);
//	printf("The max RTP: %d, task %d ",a[0].RTP, a[0].task);
//	printf("\n");


	//init dtune selection table for debug
	dtunetable = (int**)calloc(rows,sizeof(int*));
    for(i=0;i<rows;i++)
  	{
    	dtunetable[i] = (int*)calloc(cols,sizeof(int));
    	for(j=0;j<cols;j++)
    		dtunetable[i][j]=0;
    }
	//after sort.
	j=0;//index of core
	for(i=0;i<X;i++){
//		printf("The RTP: %d, task %d \n",a[i].RTP, a[i].task);
//		fprintf(stderr, "task %d ", pro_order[i]);
		if(lambda[a[i].task]==0){//NR
			objf += seltable[a[i].task][j];
			dtunetable[i][j]=1;
			j++;
		}else{//TMR
			objf += seltable[a[i].task][j+2];
			dtunetable[i][j]=1;
			dtunetable[i][j+1]=1;
			dtunetable[i][j+2]=1;
			j+=3;
		}
//		printf("j = %d \n", j);
	}
	return objf;
}

int main() {

 hungarian_problem_t p;

  /* an example cost matrix */
//  int r[5*4] =  {  10, 19, 8, 15,
//		   10, 18, 7, 17,
//		   13, 16, 9, 14,
//		   12, 19, 8, 18,
//		   14, 17, 10, 19 };

  int x = 5, y = 5;
  int** m = input_to_matrix(x, y);

#if 1
  /* initialize the gungarian_problem using the cost matrix*/
  int matrix_size = hungarian_init(&p, m , x,y, HUNGARIAN_MODE_MINIMIZE_COST) ;

  fprintf(stderr, "The version selection table:");
  hungarian_print_matrix(seltable,X, delta);

  fprintf(stderr, "assignement matrix has a now a size %d rows and %d columns with delta %d.\n\n",  matrix_size,matrix_size, delta);

  /* some output */
  fprintf(stderr, "cost-matrix:");
  hungarian_print_costmatrix(&p);

  /* solve the assignement problem */
  hungarian_solve(&p);

  /* some output */
  fprintf(stderr, "assignment:");
  hungarian_print_assignment(&p);

  //khchen
  fprintf(stderr, "HA result Cost is %d\n\n",HA_result);
  fprintf(stderr, "..........................................\n");
  if(delta!=3*X&&delta!=X)
	  fprintf(stderr, "PA result Cost is %d\n",promoting_sequence(p.assignment, p.cost, p.num_rows, p.num_cols));
//  fprintf(stderr, "The HA selection table:");
//  hungarian_print_matrix(final_assignment,X, delta);
//  fprintf(stderr, "dTune result Cost is %d\n", dtune(X,delta));
  fprintf(stderr, "The dTune selection table:");
//  hungarian_print_matrix(dtunetable,X, delta);

  printf("Ratio between dtune and PA %lf \n", (double)HA_result/dtune(X,delta));

  /* free used memory */
  hungarian_free(&p);
  /*khchen free*/
  matrix_free(seltable, X, delta);
  matrix_free(dtunetable, X, delta);
  input_datafree(R);
  input_datafree(AVG);
  version_datafree(C, 101);
  version_datafree(P, 101);
  version_datafree(SP,300);

  free(m);
#endif

  return 0;
}

