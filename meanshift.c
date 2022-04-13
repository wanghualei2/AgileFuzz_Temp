#include <math.h> 
#include <stdio.h>
#define CLUSTER_EPSILON 1.5 

#define ORIGIN_POINT 1
#define SHIFT_POINT 2
#define STOP_POINT 3
#define MAX_POINT 4000

//停止移动的阈值（当最大的移动距离小于该值时，停止进行均值移动）
int EPSILON_SQR = 1;

int cluster_width=10;

int kernel_bandwidth=20;

struct Points{
    int values[MAX_POINT]; 
    int size;
};

struct Cluster {

    double mode;

    int size; 

    int original_points[MAX_POINT];
    int shifted_points[MAX_POINT];
}; 

struct Points origin_points;

struct Points shift_points; 

struct Points stop_points; 

struct Cluster clusters[MAX_POINT];

int clusters_size=0;

void init_clusters(){
    for(int i=0;i<clusters_size;i++){
        for(int ii=0;ii<clusters[i].size;i++){
            clusters[i].original_points[ii]=0;
            clusters[i].shifted_points[ii]=0;
        }
        clusters[i].size=0;
    }
    clusters_size=0;
}


void init_point(int points_size){
    if(points_size==ORIGIN_POINT){
        for(int i=0;i<origin_points.size;i++){
            origin_points.values[i]=0; 
        }
        origin_points.size=0;
    }else if(points_size==SHIFT_POINT){

        for(int i=0;i<shift_points.size;i++){
            shift_points.values[i]=0; 
        }
        shift_points.size=0;
    }else{

        for(int i=0;i<stop_points.size;i++){
            stop_points.values[i]=0; 
        }
        stop_points.size=0;
    }

}

void add_point(int points_type,int v){
    if(points_type==ORIGIN_POINT){
        origin_points.values[origin_points.size]=v;
        origin_points.size++;
    }else if(points_type==SHIFT_POINT){
        shift_points.values[shift_points.size]=v;
        shift_points.size++;
    }else{
        stop_points.values[stop_points.size]=v;
        stop_points.size++;
    }
}

int euclidean_distance(int point_a, int point_b) { 
    if (point_a > point_b)
        return point_a - point_b;
    return point_b - point_a;
}

double gaussian_kernel(int distance, int kernel_bandwidth) {
    double temp = exp(-1.0 / 2.0 * (distance * distance) / (kernel_bandwidth * kernel_bandwidth));
    return temp;
}

int euclidean_distance_sqr(int point_a, int point_b) {
    return (point_a - point_b) * (point_a - point_b);
}

//计算单点的漂移值
int single_shift_point(int point) {
    double total_weight = 0;
    double shifted_point = 0;
    for (int i = 0; i < origin_points.size; i++) {
        const double temp_point = origin_points.values[i]; 
        double distance = euclidean_distance(point, temp_point);
        //只计算范围内的点与point的均值
        if (distance > cluster_width) { 
            continue;
        }
        //不同的点权重不一样，使用高斯核函数计算权重
        double weight = gaussian_kernel(distance, kernel_bandwidth); 
        shifted_point += (temp_point * weight);
        total_weight += weight;
    }

    double total_weight_inv = 1.0 / total_weight;
    shifted_point *= total_weight_inv;
    return (int)shifted_point;
}

void start_ShiftPoint(){
 
    init_point(STOP_POINT);
    init_point(SHIFT_POINT); 

    for (int i = 0; i < origin_points.size; i++) { 
        add_point(SHIFT_POINT,origin_points.values[i]);
    }  

    int max_shift_distance;

    int shift_point = 0;
    do {
        max_shift_distance = 0;
        for (int i = 0; i < origin_points.size; i++) {
            if (stop_points.values[i] == 0) { 
                //计算均值
                shift_point=single_shift_point(shift_points.values[i]);
                //计算当前点移动的距离
                int shift_distance_sqr = euclidean_distance_sqr(shift_point, shift_points.values[i]);

                if (shift_distance_sqr > max_shift_distance) {
                    max_shift_distance = shift_distance_sqr;
                }
                if (shift_distance_sqr <= EPSILON_SQR) {
                    stop_points.values[i] = 1;
                    add_point(STOP_POINT,1);
                }
                shift_points.values[i] = shift_point; 
            }
        }  
    } while (max_shift_distance > EPSILON_SQR);   
}

void printf_points(int points_type){
    if(points_type==ORIGIN_POINT){
        printf("origin points:\n");
        for(int i=0;i<origin_points.size;i++){
            printf("%d,",origin_points.values[i]);
        }
        printf("\n");
    }else if(points_type==SHIFT_POINT){
        printf("shift points:\n");
        for(int i=0;i<shift_points.size;i++){
            printf("%d,",shift_points.values[i]);
        }
        printf("\n");
    } 
}

void printf_cluster(){

    printf("cluster:\n");

    for(int i=0;i<clusters_size;i++){
        if(clusters[i].size==1){
            printf(",%d",clusters[i].original_points[0]);
        }else{
            printf(",(%d:%d,%d)",clusters[i].size,clusters[i].original_points[0],clusters[i].original_points[clusters[i].size-1]);
        }
    }
    printf("\n");
}

void start_cluster()
{  

    for (int i = 0; i < shift_points.size; i++) { 
         
        int c = 0;
        for (; c < clusters_size; c++) { 
            if (euclidean_distance(shift_points.values[i], clusters[c].mode) <= CLUSTER_EPSILON) {
                break;
            }
        } 
        if (c == clusters_size) { 
            clusters[clusters_size].mode=shift_points.values[i]; 
            clusters_size+=1;
        }  
        if (clusters[c].mode < shift_points.values[i])
            clusters[c].mode = shift_points.values[i];
 
        clusters[c].original_points[clusters[c].size]=origin_points.values[i];
        clusters[c].shifted_points[clusters[c].size]=shift_points.values[i];
        clusters[c].size+=1;

    }  
}


void main(){ 

    double nums[]={1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,40,41,42,43,44};
    // double nums[]={1988,2043,2044,2045,2046,2050,2051,2052,2979,5590,5912,6045,6046,6047,6048,6049,6050,6051,6052,6053,6054,6055,6056,6057,6058,6059,6060,6061,6062,6063,6064,6065,7549,7672,7673};
 
	int size=sizeof(nums)/sizeof(double);
	for(int i=0;i<size;i++){ 
	    add_point(ORIGIN_POINT,nums[i]); 
	}  
    printf("%d\n",origin_points.size);



    start_ShiftPoint();
    printf_points(ORIGIN_POINT);
    printf_points(SHIFT_POINT);

    start_cluster();

    printf_cluster();


}
