library(mvtnorm)
library(mgcv)
library(fields)
library(akima)

# B splines
basis <- function(x, degree, i, knots) {
  if(degree == 0){
    B <- ifelse((x >= knots[i]) & (x < knots[i+1]), 1, 0)
  } else {
    if((knots[degree+i] - knots[i]) == 0) {
      alpha1 <- 0
    } else {
      alpha1 <- (x - knots[i])/(knots[degree+i] - knots[i])
    }
    if((knots[i+degree+1] - knots[i+1]) == 0) {
      alpha2 <- 0
    } else {
      alpha2 <- (knots[i+degree+1] - x)/(knots[i+degree+1] - knots[i+1])
    }
    B <- alpha1*basis(x, (degree-1), i, knots) + alpha2*basis(x, (degree-1), (i+1), knots)
  }
  return(B)
}

make.BS <- function(u, degree=3, interior.knots=seq(0.1,0.9,length=9), intercept=TRUE, Boundary.knots = c(0,1)) {
  if(missing(u)) stop("You must provide u")
  if(degree < 1) stop("The spline degree must be at least 1")
  Boundary.knots <- sort(Boundary.knots)
  interior.knots.sorted <- NULL
  if(!is.null(interior.knots)) interior.knots.sorted <- sort(interior.knots)
  knots <- c(rep(Boundary.knots[1], (degree+1)), interior.knots.sorted, rep(Boundary.knots[2], (degree+1)))
  K <- length(interior.knots) + degree + 1
  B.mat <- matrix(0,length(u),K)
  for(j in 1:K) B.mat[,j] <- basis(u, degree, j, knots)
  if(any(u == Boundary.knots[2])) B.mat[u == Boundary.knots[2], K] <- 1
  if(intercept == FALSE) {
    return(B.mat[,-1])
  } else {
    return(B.mat)
  }
}

make.theta<-function(x,delta.star){x%*%make.alpha(delta.star)}

make.mu<-function(u,x,delta.star){
  theta<-make.theta(x,delta.star)
  apply(t(sapply(u,make.BS))*theta,1,sum)} 

make.mu.one<-function(u,theta){sum(make.BS(u)*theta)}

make.alpha<-function(delta.star){
  delta<-make.delta(delta.star)
  t(apply(t(delta),2,cumsum))} 

make.delta<-function(D){
  delta<-D
  for(j in 2:ncol(D)){
    delta[,j]<-make.delta.one(D[,j])
  }
  delta}

make.delta.one<-function(D){
  if(D[1]+sum(ifelse(D[-1]<0,D[-1],0))<0){D<-0*D}
  D}

llike<-function(y,x,B,ds,tau){
  nt<-length(y)
  theta<-make.theta(x,ds)
  Q<-theta%*%t(B)
  lll<-slope<-u<-rep(0,nt)
  if(prod(y>Q[,1] & y<Q[,ncol(Q)])){ 
    for(j in 1:nt){
      lower<-sum(Q[j,]<=y[j])
      if(lower==ncol(Q)){lower<-lower-1}
      slope[j]<-Q[j,lower+1]-Q[j,lower]
    }
    lll<- -log(slope)
  }
  list(lll=lll)}

q<-function(ds,B,j){
  alpha<-t(make.alpha(ds))
  B%*%alpha[,j]}

mn.baseline.t<-function(Theta,n.knots,n.tau=100,lambda=1,main="",make.plot=F){
  library(sn)
  tau<-seq(0.02,0.98,length=n.tau)
  B=make.BS(tau)
  DIFF<-diag(n.knots);DIFF[lower.tri(DIFF)]<-1
  B<-B%*%DIFF
  Ain<-diag(n.knots)[-1,]
  bigB<-rbind(B,lambda*Ain)
  qqq<-qsn(tau,dp=Theta[1:3],solver="RFB")
  bigQ<-c(qqq,rep(0,n.knots-1))
  w<-c(1.1-qqq*(1-qqq),rep(0,n.knots-1))
  coefs<-pcls(list(y=bigQ,X=bigB,C=matrix(0,0,0),
                   p=rep(1,n.knots),w=w,
                   Ain=Ain,bin=rep(0,n.knots-1)))
  coefs}

prior.theta<-function(Theta){
  R<-dnorm(Theta[1],30,100,log=T)+   
     dunif(Theta[2],0,35,log=T)+ 
     dnorm(Theta[3],0,10,log=T)+
     dunif(Theta[4],30,100,log=T)
     sum(R)}

makeplot<-function(x,data,main=""){
  out.p<-interp(x[,1],x[,2],data,duplicate="mean")
  zlim<-range(data)
  image.plot(out.p,xlim=c(0,1),ylim=c(0,1),zlim=zlim,main=main)
  contour(out.p,add=T,nlevels=10)
}

nk = 3 + 9 + 1 

Bayes.QReg.BS<-function(y,x,long,lat,n.knots=nk,coru=T,corquants=F,spacevar=T,
                        keep.s=NULL,keep.X=NULL,
                        mn.range=.5,sd.range=1,eps=0.1,
                        quants=seq(0.1,0.9,0.1),
                        runs=5000,burn=1000,update=10,min.q=0.1,max.q=0.9){
  par(mar=c(0.1,0.1,0.1,0.1))
  n.q<-length(quants)
  nt<-nrow(y)
  ns=n.sites=ncol(y)
  p<-dim(x)[2]
  d<-as.matrix(dist(cbind(long,lat),upper=TRUE,diag=TRUE))
  
  MISS<-is.na(y)
  for(t in 1:nt){y[t,MISS[t,]]<-mean(na.omit(y[t,]))}
  
  betahat<-array(0,c(n.q,p,ns))
  for(s in 1:ns){for(j in 1:n.q){
    betahat[j,,s]<-rq(y[,s]~x[,-1,s],tau=quants[j])$coef
  }}
  
  tau.grid<-seq(0.0,1.00,length=100)
  
  B.grid<-make.BS(tau.grid)
  
  B.quants<-make.BS(quants)
  
  ds <- array(runif(p*n.knots*ns),c(p,n.knots,ns))
  ds[1,1,]<-apply(y,2,min)-.1
  ds[1,n.knots,]<-apply(y,2,max)-ds[1,1,]+.1
  
  mn.ds<-prec.ds<-matrix(1,p,n.knots)
  
  range.ds<-rep(mn.range,p)
  mn.mn.ds<-prec.mn.ds<-rep(eps,p)
  COR.ds<-PREC.ds<-array(0,c(ns,ns,p))
  
  for(j in 1:p){ 
    COR.ds[,,j]<-exp(-d/range.ds[j])
    PREC.ds[,,j]<-solve(COR.ds[,,j])
  }
  
  dev<-rep(0,runs)
  keeprange.ds<-matrix(0,runs,p)
  keepqfx<-array(0,c(runs,n.q,p,ns)) 
  n.basisfx<-matrix(0,n.knots,n.sites)
  MH.range<-rep(.50,p+1);MH.range[p+1]<-0.10
  acc.range<-att.range<-rep(0,p+1)
  acc<-att<-matrix(0,p,n.knots)
  init.MH<-0.2*sd(na.omit(as.vector(y)))
  MH<-matrix(init.MH,p,n.knots)
  a.range<-(mn.range/sd.range)^2
  b.range<-log(20)*mn.range/(sd.range^2)
  mmm<-mean(na.omit(as.vector(y)))
  sss<-sd(na.omit(as.vector(y)))
  Theta<-c(mmm,sss/10,.1,50) 
  MH.Theta<-c(sss/5,sss/5,1,5)
  acc.Theta<-att.Theta<-0*MH.Theta
  q0hat<-mn.baseline.t(Theta,n.knots)
  keepTheta<-matrix(0,runs,4)
  

  curll<-matrix(0,nt,ns)
  for(s in 1:ns){
    xxx<-llike(y[,s],x[,,s],B.grid,ds[,,s],tau.grid)
    curll[,s]<-xxx$lll
  }
  
  for(i in 1:runs){
    if(sum(MISS)>0){for(t in 1:nt){if(sum(MISS[t,])>0){
      cany<-y;canll<-curll
      for(s in 1:ns){if(MISS[t,s]){
        cany[t,s]<-y[t,s]+0.5*sd(y[,s])*rnorm(1)
        xxx<-llike(cany[t,s],x[t,,s],B.grid,ds[,,s],tau.grid)
        canll[t,s]<-xxx$lll 
      }}
      R<-sum(canll[t,]-curll[t,])
      if(!is.na(exp(R))){if(min(canll[t,])!=-Inf){if(runif(1)<exp(R)){
        y<-cany;curll<-canll
      }}}
    }}}
    
    for(j in 1:p){for(s in 1:ns){for(l in 1:n.knots){
      att[j,l]<-att[j,l]+1
      cands<-ds;canll<-curll
      cands[j,l,s]<-rnorm(1,ds[j,l,s],MH[j,l]/p)  
      SD<-1/sqrt(prec.ds[j,l]*PREC.ds[s,s,j])
      MN<-SD*SD*(prec.ds[j,l]*(PREC.ds[s,s,j]*mn.ds[j,l]-
                                 PREC.ds[s,-s,j]%*%(ds[j,l,-s]-mn.ds[j,l])))
      R<-dnorm(cands[j,l,s],MN,SD,log=T)-dnorm(ds[j,l,s],MN,SD,log=T)
      
      bothzero<-sum(make.delta.one(ds[,l,s])^2+make.delta.one(cands[,l,s])^2)==0 & l>1
      if(!bothzero){
        xxx<-llike(y[,s],x[,,s],B.grid,cands[,,s],tau.grid)
        canll[,s]<-xxx$lll
        R<-R+sum(canll[,s]-curll[,s]) 
      }
      if(!is.na(exp(R))){if(min(canll[,s])> -Inf){if(runif(1)<exp(R)){
        ds<-cands;curll<-canll;acc[j,l]<-acc[j,l]+1
      }}}
      
    }}}  
    
    for(j in 1:p){
      PREC.ds.vec<-apply(PREC.ds[,,j],1,sum)
      PREC.ds.sum<-sum(PREC.ds[,,j])
      SSS<-PREC<-MN<-rep(0,n.knots)
      for(l in 1:n.knots){
        SSS[l]<-t(ds[j,l,]-mn.ds[j,l])%*%PREC.ds[,,j]%*%(ds[j,l,]-mn.ds[j,l])
      }
      prec.ds[j,1]<-rgamma(1,ns/2+eps,rate=SSS[1]/2+eps)
      prec.ds[j,2:n.knots]<-rgamma(1,(n.knots-1)*ns/2+eps,sum(SSS[-1])/2+eps)
      
    }
    
    mn.ds<-0*mn.ds; 
    mn.ds[1,]<-q0hat
    
    for(j in 1:length(Theta)){
      att.Theta[j]<-att.Theta[j]+1
      canTheta<-Theta
      canTheta[j]<-rnorm(1,Theta[j],MH.Theta[j])
      R<-prior.theta(canTheta)-prior.theta(Theta)
      if(R> -Inf){
        canq0hat<-mn.baseline.t(canTheta,n.knots)
        for(l in 1:n.knots){
          dnew<-ds[1,l,]-canq0hat[l]
          dold<-ds[1,l,]-q0hat[l]
          R<-R-0.5*prec.ds[1,l]*t(dnew)%*%PREC.ds[,,1]%*%dnew+
            0.5*prec.ds[1,l]*t(dold)%*%PREC.ds[,,1]%*%dold
        }
        if(!is.na(R)){if(runif(1)<exp(R)){Theta<-canTheta;q0hat<-canq0hat;
        acc.Theta[j]<-acc.Theta[j]+1}}
        if(runif(1)<exp(R)){Theta<-canTheta;q0hat<-canq0hat;
        acc.Theta[j]<-acc.Theta[j]+1}
      }
    }
    
    mn.ds<-0*mn.ds; 
    mn.ds[1,]<-q0hat
    
    if(corquants){for(j in 1:p){ 
      att.range[j]<-att.range[j]+1
      canrange.ds<-rnorm(1,range.ds[j],MH.range[j]*sd.range)
      if(canrange.ds>0){
        canCOR.ds<-exp(-d/canrange.ds)
        canPREC.ds<-solve(canCOR.ds)
        canlogD<-determinant(canPREC.ds,logarithm=TRUE)$modulus
        logD<-determinant(PREC.ds[,,j],logarithm=TRUE)$modulus
        R<-0.5*n.knots*(canlogD-logD)+
          dgamma(canrange.ds,a.range,b.range,log=T)-
          dgamma(range.ds[j],a.range,b.range,log=T)
        for(l in 1:n.knots){
          ds.std<-sqrt(prec.ds[j,l])*(ds[j,l,]-mn.ds[j,l])
          R<-R-0.5*t(ds.std)%*%canPREC.ds%*%ds.std+
            0.5*t(ds.std)%*%PREC.ds[,,j]%*%ds.std
        }
        if(runif(1)<exp(R)){range.ds[j]<-canrange.ds;COR.ds[,,j]<-canCOR.ds;acc.range[j]<-acc.range[j]+1}
        PREC.ds[,,j]<-solve(COR.ds[,,j])
      }
    }}
    
    if(!corquants){for(j in 1:p){COR.ds[,,j]<-PREC.ds[,,j]<-diag(ns)}}
    
    if(i<burn/2){for(j in 1:p){for(l in 1:n.knots){if(att[j,l]>100){
      if(acc[j,l]/att[j,l]<0.3){MH[j,l]<-MH[j,l]*0.8}
      if(acc[j,l]/att[j,l]>0.5){MH[j,l]<-MH[j,l]*1.2}
      acc[j,l]<-att[j,l]<-0
    }}}}

    MH[MH<0.1*init.MH]<-0.1*init.MH
    
    if(i<burn/2){for(j in 1:(p+1)){if(att.range[j]>25){
      if(acc.range[j]/att.range[j]<0.3){MH.range[j]<-MH.range[j]*0.7}
      if(acc.range[j]/att.range[j]>0.5){MH.range[j]<-MH.range[j]*1.3}
      acc.range[j]<-att.range[j]<-0
    }}}
    
    MH.range[MH.range<0.01]<-0.01
    if(i<burn/2){for(j in 1:4){if(att.Theta[j]>50){
      if(acc.Theta[j]/att.Theta[j]<0.3){MH.Theta[j]<-MH.Theta[j]*0.8}
      if(acc.Theta[j]/att.Theta[j]>0.5){MH.Theta[j]<-MH.Theta[j]*1.2}
      acc.Theta[j]<-att.Theta[j]<-0
    }}}
    MH.Theta[MH.Theta<0.1]<-0.1
    
    keeprange.ds[i,]<-range.ds
    dev[i]<--2*sum(curll)
    keepTheta[i,]<-Theta
    
    
    for(s in 1:ns){for(j in 1:p){
      #print(ds)
      keepqfx[i,,j,s]<-q(ds[,,s],B.quants,j) # this is the estimates
    }}
    
    if(i>burn){for(l in 1:n.knots){for(s in 1:n.sites){
      n.basisfx[l,s]<-n.basisfx[l,s]+
        (sum(abs(make.delta.one(ds[,l,s])))!=0)/(runs-burn)
    }}}
    
    if(i%%update==0){
      par(mfrow=c(3,3))
      plot(exp(-0.5*median(d)/keeprange.ds[1:i,1]),type="l",ylim=c(0,1))
      for(j in p:1){lines(exp(-0.5*median(d)/keeprange.ds[1:i,j]),col=j)}
      plot(keepTheta[1:i,1],ylim=range(keepTheta[1:i,1:3]),type="s",col=1)
      for(j in 2:length(Theta)){lines(keepTheta[1:i,j],col=j,type="s")}
      
    }
    
  }
  
  list(dev=dev,qfx=keepqfx,range.ds=keeprange.ds,n.basisfx=n.basisfx,
       Theta=keepTheta)}