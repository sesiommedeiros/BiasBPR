###################################################################
# Improved estimators in beta prime regression models 
# Application
# Francisco M.C. Medeiros, Mariana C. Araújo, Marcelo Bourguignon
# AStA Advances in Statistical Analysis
# Date: 18/08/2020
#################################################################### 

library(car)
library(Matrix)
library(compiler)
library(extraDistr)
library(nleqslv)
library(xtable)
source("gamlss_BP.R")

#####################################################################################
#             DATA 
#####################################################################################

dry = c(0.2013, 0.1987, 0.2015, 0.2014, 0.2042, 0.2003, 0.2055, 0.2013, 0.2031, 
      0.2014, 0.1958, 0.2000, 0.2017, 0.1866, 0.1783, 0.2006, 0.2031, 0.2025, 
      0.2013, 0.2016, 0.2005, 0.2067, 0.1998, 0.2002, 0.1566, 0.1332, 0.2075)

wet = c(1.15, 0.83, 0.96, 1.39, 1.74, 1.41, 1.92, 2.17, 0.98, 1.75, 0.90, 
        1.22, 1.65, 1.01, 0.90, 1.67, 1.94, 1.79, 1.84, 1.29, 1.73, 1.82, 
        2.23, 2.05, 0.71, 0.69, 1.81)

cs  = c(0.11, 0.09, 0.08, 0.01, 0.0, 0.09, 0.09, 0.10, 0.09, 0.08, 0.09,
        0.08, 0.10, 0.11, 0.11, 0.12, 0.10, 0.10, 0.10, 0.11, 0.11, 0.11, 
        0.10, 0.10, 0.15, 0.18, 0.12)


rb = 1000              # Bootstrap replications
p = 3                  #dimensions of beta
q = 2                  # dimensions of gamma
n  = length(dry)
X  =  matrix(c(rep(1,n), wet, cs), ncol = p)
Z  = matrix(c(rep(1,n), wet), ncol = q)
Dobs = dry

#####################################################################
#          FISHER INFORMATION
#####################################################################
InfFisher <- function(x){
	beta1 = matrix(x[1:p], ncol=1)
  nu1 = matrix(x[-(1:p)], ncol=1)
  eta1.est = X%*%beta1
  eta2.est = Z%*%nu1
      
	mu.est <- as.vector(exp(eta1.est))
	phi.est <- as.vector(exp(eta2.est))

  dg1 <- psigamma(mu.est*(1+phi.est), deriv=1)
 	dg11 <- psigamma(mu.est*(1+phi.est) + phi.est + 2, deriv=1)
  dg12 <- psigamma(phi.est + 2, deriv=1)
	dg2 <- psigamma(mu.est*(1+phi.est), deriv=2)
	dg21 <- psigamma(mu.est*(1+phi.est) + phi.est + 2, deriv=2)
  dg22 <- psigamma(phi.est + 2, deriv=2)

	a1 <- dg1 - dg11
  b1 <- mu.est^2*dg1 - (1+mu.est)^2*dg11 + dg12
	c1 <- dg2 - dg21
	d1 <- (1+mu.est)^2*dg21 - mu.est^2*dg2
	e1 <- (1+mu.est)^3*dg21 - mu.est^3*dg2 - dg22
 	
  E1 <- diag((1+phi.est)^2*(a1)*mu.est^2)
  E2 <- diag((1+phi.est)*(mu.est*a1 - dg11)*mu.est*phi.est)
  E4 <- diag(b1*phi.est^2)

  K11 <- t(X)%*%E1%*%X
	K12 <- t(X)%*%E2%*%Z
	K21 <- t(K12)
	K22 <- t(Z)%*%E4%*%Z
  k1 <- cbind(K11, K12)
  k2 <- cbind(K21, K22)
  IE <- rbind(k1, k2)
  K <- solve(IE)
  return(diag(K))

}

#####################################################################
#          BIAS OF THE BETA AND NU - COX-SNELL
#####################################################################
bias <- function(x){ 
  beta1 = matrix(x[1:p], ncol=1)
  nu1 = matrix(x[-(1:p)], ncol=1)
  eta1.est = X%*%beta1
  eta2.est = Z%*%nu1
      
	mu.est <- as.vector(exp(eta1.est))
	phi.est <- as.vector(exp(eta2.est))

  dg1 <- psigamma(mu.est*(1+phi.est), deriv=1)
 	dg11 <- psigamma(mu.est*(1+phi.est) + phi.est + 2, deriv=1)
  dg12 <- psigamma(phi.est + 2, deriv=1)
	dg2 <- psigamma(mu.est*(1+phi.est), deriv=2)
	dg21 <- psigamma(mu.est*(1+phi.est) + phi.est + 2, deriv=2)
  dg22 <- psigamma(phi.est + 2, deriv=2)

	a1 <- dg1 - dg11
  b1 <- mu.est^2*dg1 - (1+mu.est)^2*dg11 + dg12
	c1 <- dg2 - dg21
	d1 <- (1+mu.est)^2*dg21 - mu.est^2*dg2
	e1 <- (1+mu.est)^3*dg21 - mu.est^3*dg2 - dg22

  m1 <- -( (1+phi.est)^3*c1*(mu.est)^3 )/2 - ( (1+phi.est)^2*a1*mu.est*mu.est )/2 
	m2 <- ( (1+phi.est)*(-a1*mu.est + dg11)*mu.est*phi.est )/2 - ( (1+phi.est)^2*(mu.est*c1 - dg21)*mu.est^2*phi.est )/2
	m3 <- - ( (1+phi.est)*( 2*a1 + (1+phi.est)*mu.est*c1 - (1+phi.est)*dg21 )*mu.est^2*phi.est )/2  - ( (1+phi.est)*(dg11 - a1*mu.est)*mu.est*phi.est )/2
	m4 <- ( (1+phi.est)*d1 + 2*dg11 - 2*mu.est*a1 )*mu.est*phi.est^2/2 - ( (1+phi.est)*(dg11 - mu.est*a1)*mu.est*phi.est )/2
	m5 <- ( (1+phi.est)*d1/2 )*phi.est^2*mu.est + ( (1+phi.est)*(dg11 - mu.est*a1)*mu.est*phi.est )/2
	m6 <- (e1*phi.est^3 - b1*phi.est*phi.est)/2

  M1 <- diag(m1)
	M2 <- diag(m2)
	M3 <- diag(m3)
	M4 <- diag(m4)
	M5 <- diag(m5)
	M6 <- diag(m6)
 	
  E1 <- diag((1+phi.est)^2*(a1)*mu.est^2)
  E2 <- diag((1+phi.est)*(mu.est*a1 - dg11)*mu.est*phi.est)
  E4 <- diag(b1*phi.est^2)

  K11 <- t(X)%*%E1%*%X
	K12 <- t(X)%*%E2%*%Z
	K21 <- t(K12)
	K22 <- t(Z)%*%E4%*%Z
  k1 <- cbind(K11, K12)
  k2 <- cbind(K21, K22)
  IE <- rbind(k1, k2)
  K <- solve(IE)

	Kbb <- K[1:p,1:p]
  Kbnu <- K[1:p,(p+1):(p+q)]
  Knub <- t(Kbnu)
  Knunu <- K[(p+1):(p+q),(p+1):(p+q)]
	Pbb <- matrix(diag(X%*%Kbb%*%t(X)))
	Pbnu <- matrix(diag(X%*%Kbnu%*%t(Z)))
	#Pnub <- t(Pbnu)
	Pnunu <- matrix(diag(Z%*%Knunu%*%t(Z)))
	
  biasbeta <- Kbb%*%t(X)%*%(M1%*%Pbb +(M2+M3)%*%Pbnu + M5%*%Pnunu) + Kbnu%*%t(Z)%*%(M2%*%Pbb +(M4+M5)%*%Pbnu + M6%*%Pnunu)

	biasnu <- Knub%*%t(X)%*%(M1%*%Pbb +(M2+M3)%*%Pbnu + M5%*%Pnunu) + Knunu%*%t(Z)%*%(M2%*%Pbb +(M4+M5)%*%Pbnu + M6%*%Pnunu)
      
  return(c(biasbeta, biasnu))
}

#####################################################################
#          VECTOR SCORE - DAVID FIRTH
#####################################################################
score_DF <- function(x, v){
  U           = numeric(p+q)
  beta.df     = matrix(x[1:p], ncol=1)
  nu.df       = matrix(x[-(1:p)], ncol=1)
  eta1.est.df = X%*%beta.df
  eta2.est.df = Z%*%nu.df
      
	mu.est.df   = as.vector(exp(eta1.est.df))
	phi.est.df  = as.vector(exp(eta2.est.df))
   
  dg1         = psigamma(mu.est.df*(1+phi.est.df), deriv=1)
 	dg11        = psigamma(mu.est.df*(1+phi.est.df) + phi.est.df + 2, deriv=1)
  dg12        = psigamma(phi.est.df + 2, deriv=1)

  a1 = dg1 - dg11
  b1 = mu.est.df^2*dg1 - (1+mu.est.df)^2*dg11 + dg12

	E1 = diag((1+phi.est.df)^2*(a1)*mu.est.df^2)
  E2 = diag((1+phi.est.df)*(mu.est.df*a1 - dg11)*mu.est.df*phi.est.df)
  E4 = diag(b1*phi.est.df^2)

  K11 = t(X)%*%E1%*%X
	K12 = t(X)%*%E2%*%Z
	K21 = t(K12)
	K22 = t(Z)%*%E4%*%Z
  k1  = cbind(K11, K12)
  k2  = cbind(K21, K22)
  IE  = rbind(k1, k2)
   
  A        = matrix(x, ncol=p+q)
  res.bias = bias(A)
  vies     = matrix(c(res.bias), ncol=1) 
    
  M       = IE%*%vies
  PHI     = diag(1+phi.est.df)
  D1      = diag(mu.est.df)
  y.star  = matrix(log(v/(1+v)), ncol=1)
  mu.star = matrix(psigamma(mu.est.df*(1+phi.est.df), deriv=0) - psigamma(mu.est.df*(1+phi.est.df) + phi.est.df + 2, deriv=0), ncol=1)
  D2      = diag(phi.est.df)
  v.nu    = matrix(mu.est.df*(y.star-mu.star) + psigamma(mu.est.df*(1+phi.est.df) + phi.est.df + 2, deriv=0) - log(1+v) - psigamma(2+phi.est.df, deriv=0), ncol=1 )
 
  U.beta  = t(X)%*%PHI%*%D1%*%(y.star-mu.star)
  U.nu    = t(Z)%*%D2%*%v.nu
  U       = c(as.vector(U.beta) - M[1:p] , as.vector(U.nu) - M[(p+1):(p+q)] )
  	# print(U)
  U
	}

#####################################################################
#          BIAS OF THE BETA AND NU - BOOTSTRAP
#####################################################################
 bp.fun <- function(data, est.b){
    eta1.est.boot <- X%*%est.b[1:p]
    eta2.est.boot <- Z%*%est.b[-(1:p)]
    mu.est.boot <- as.vector(exp(eta1.est.boot))
	  nu.est.boot <- as.vector(exp(eta2.est.boot))
    est.bootp <- matrix(NA,rb,p+q)
    
    set.seed(2020)
    Dobs_b <- matrix(mapply(rBP, rb, mu.est.boot, nu.est.boot), nr = rb)

    calc_boot <- function(dadosb){
      	loglik_boot <- function(vp){
         beta_boot <- vp[1:p]
         nu_boot <- vp[-(1:p)]
         eta1_boot   <- as.vector(X%*%beta_boot)
         eta2_boot   <- as.vector(Z%*%nu_boot)
         mu_boot    <- exp(eta1_boot)
         phi_boot <- exp(eta2_boot)
    
         a_boot <- mu_boot*(1+phi_boot)
         b_boot <- 2 + phi_boot 
    
         fy_boot <- (a_boot-1)*log(dadosb) - (a_boot+b_boot)*log(1+dadosb) - lbeta(a_boot,b_boot)
    
        return(sum(fy_boot))
       		 }
    v0 <- est.b
    est_bootp <- try(optim(v0, loglik_boot, method = "BFGS", control=list(fnscale=-1)),T)
		if(class(est_bootp)=="try-error"){
			estb = rep(NA, p+q)
     		 }else{
               	estb = est_bootp$par
             }
            return(estb)
       }
    calc_bootb = match.fun(calc_boot)
    resultb = t(apply(Dobs_b, 1, calc_boot))
    return(resultb) 
}

	
########################################################################################
#                         M.A.I.N   F.U.N.C.T.I.O.N
########################################################################################
  conh = gamlss.control(trace = FALSE, autostep = FALSE, save = TRUE)
  fit   = gamlss(dry~wet+cs,dry~wet,family=BP(mu.link="log",sigma.link = "log"),
                 control=conh,method=RS())
  
  beta.est.mv = fit$mu.coefficients
  nu.est.mv   = fit$sigma.coefficients
      
  A = c(beta.est.mv, nu.est.mv)
  res.bias = bias(A)

  #####################################################################
  #     COX-SNELL
  #####################################################################
  vies.beta.cs <- res.bias[1:p]
  vies.nu.cs <- res.bias[-(1:p)]

  beta.est.cs = beta.est.mv - vies.beta.cs    
  nu.est.cs = nu.est.mv - vies.nu.cs
      
  #####################################################################
  #     DAVID FIRTH
  #####################################################################
  est.mv = c(beta.est.mv,nu.est.mv)
  est_df = nleqslv(est.mv, score_DF, method="Broyden",global="hook",jacobian=TRUE, control=list(btol=1e-7), v=Dobs) #control=list(trace=0,maxit=500,allowSingular=TRUE, cndtol=1e-5)
  beta.est.df = est_df$x[1:p]  
  nu.est.df = est_df$x[-(1:p)]
  
  #####################################################################
  #     PARAMETRIC BOOTSTRAPPING
  #####################################################################
  results_bootp = data.frame(bp.fun(Dobs, est.mv))
  est.bp = apply(results_bootp, 2, mean)
  beta.est.boot = 2*beta.est.mv - est.bp[1:p]
  nu.est.boot = 2*nu.est.mv - est.bp[-(1:p)]
  #####################################################################
  
  #####################################################################
  #                          RESULTS 
  #####################################################################
  result_est = c(beta.est.mv, nu.est.mv, beta.est.cs, nu.est.cs, 
                 beta.est.df, nu.est.df, beta.est.boot, nu.est.boot)
  
  #####################################################################
  #                       PARAMETER ESTIMATES 
  #####################################################################
  nEst = matrix(round(c(result_est),4), ncol=4)
  colnames(nEst) = c("MLE", "Cox-Snell", "Firth", "p-boot")
  rownames(nEst) = c("beta0","beta1","beta2","nu0", "nu1")
  
  print.est <- function(par){
      cat("\n Beta's estimates: \n")
      print(par[1:p,])
      cat("\n Nu's estimates:\n") 
      print(par[(p+1):(p+q),])
    }
  print.est(nEst)
  
  ####################################################################
  #                 STANDARD ERROR
  ####################################################################
  variance = data.frame(apply(nEst, 2, InfFisher))
  erro.pd  = round(sqrt(variance), 4)
  rownames(erro.pd) = c("b0","b1","b2","nu0", "nu1")
  print.se <- function(par){
    cat("\n standard error - beta's: \n")
    print(par[1:p,])
    cat("\n standard error - nu's:\n") 
    print(par[(p+1):(p+q),])
  }
  print.se(erro.pd)
  
  
  
  
  
  
  
  
  
  
  
 




