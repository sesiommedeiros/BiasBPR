
####################################################################
#
# This script was obtained from 
# https://github.com/santosneto/simbp/blob/master/R/Codes.R
#
###################################################################@

library(Formula)
library(LaplacesDemon)
library(ggplot2)
library(extraDistr)
library(gamlss)

############################################################################
#              Probability Density Function
###########################################################################
dBP <- function(x,mu=1,sigma=1,log=FALSE)
{
  if (any(mu < 0)) 
    stop(paste("mu must be positive", "\n", ""))
  if (any(sigma < 0)) 
    stop(paste("sigma must be positive", "\n", ""))
  if (any(x <= 0)) 
    stop(paste("x must be positive", "\n", ""))
  
  a <- mu*(1+sigma)
  b <- 2 + sigma 
  
  fy <- dbetapr(x, shape1 = a, shape2 = b, scale = 1, log = log)
  fy
  
}

#############################################################################
#               Cumulative Distribution Function 
############################################################################
pBP <-  function(q,mu=1,sigma=1, lower.tail = TRUE, log.p = FALSE)
{
  if (any(mu < 0)) 
    stop(paste("mu must be positive", "\n", ""))
  if (any(sigma < 0)) 
    stop(paste("sigma must be positive", "\n", ""))
  if (any(q < 0)) 
    stop(paste("q must be positive", "\n", ""))
  
  a <- mu*(1+sigma)
  b <- 2 + sigma
  
  cdf <- pbetapr(q, shape1 = a, shape2 = b, scale=1, lower.tail = lower.tail, 
               log.p = log.p)
  cdf
}

#############################################################################
#                              Random Numbers
#############################################################################
rBP <- function(n,mu=1,sigma=1)
{
  if (any(mu < 0)) 
    stop(paste("mu must be positive", "\n", ""))
  if (any(sigma < 0)) 
    stop(paste("sigma must be positive", "\n", ""))
  if (any(n <= 0)) 
    stop(paste("n must be a positive integer", "\n", ""))
  
  n <- ceiling(n)
  
  a <- mu*(1+sigma)
  b <- 2 + sigma  
  
  r <- rbetapr(n,shape1=a,shape2=b,scale=1)
  
  r
}

#############################################################################
#                           Quantile Function
############################################################################
qBP <- function(p, mu = 1, sigma = 1, lower.tail = TRUE, log.p = FALSE)
{
  if (any(mu < 0)) 
    stop(paste("mu must be positive", "\n", ""))
  if (any(sigma < 0)) 
    stop(paste("sigma must be positive", "\n", ""))
  if (any(n <= 0)) 
    if (any(p <= 0) | any(p >= 1)) 
      stop(paste("p must be between 0 and 1", "\n", ""))  
  
  a <- mu*(1+sigma)
  b <- 2 + sigma 
  
  q <- qbetapr(p, shape1 = a, shape2 = b,scale=1, lower.tail = lower.tail, log.p = log.p)
  
  q
}  


#############################################################################
#                           family
############################################################################
BP <- function (mu.link = "log", sigma.link = "log") 
{
  mstats <- checklink("mu.link", "Beta Prime", substitute(mu.link), c("log", "identity", "sqrt"))
  dstats <- checklink("sigma.link", "Beta Prime",substitute(sigma.link), c("log", "identity", "sqrt"))
  structure(list(family = c("BP", "Beta Prime"), 
                 parameters = list(mu = TRUE,sigma = TRUE), nopar = 2, type = "Continuous", 
                 mu.link = as.character(substitute(mu.link)), 
                 sigma.link = as.character(substitute(sigma.link)), 
                 mu.linkfun = mstats$linkfun, 
                 sigma.linkfun = dstats$linkfun, 
                 mu.linkinv = mstats$linkinv, 
                 sigma.linkinv = dstats$linkinv, 
                 mu.dr = mstats$mu.eta, 
                 sigma.dr = dstats$mu.eta, 
                 
                 
                 dldm = function(y, mu, sigma){
                 a <- mu*(1+sigma)
                 b <- mu*(1+sigma)+sigma+2
                 Phi <-  (1+sigma)  
                 yast <- log(y) - log(1+y) 
                 muast <- digamma(a) - digamma(b) 
                 dldm <- Phi*(yast - muast)
                 
                 dldm
                 }, 
                 d2ldm2 = function(mu, sigma){ 
                   Phi2 <- (1+sigma)^2
                   a <- mu*(1+sigma)
                   b <- mu*(1+sigma)+sigma+2
                   d2dldm2 <- -Phi2*(trigamma(a) - trigamma(b))
                   
                   d2dldm2
                   },
                 dldd = function(y, mu, sigma){ 
                   Phi <-  (1+sigma)
                   a <- mu*(1+sigma)
                   b <- mu*(1+sigma)+sigma+2 
                   ystar <- mu*log(y) - (1+mu)*log(1+y) 
                   mustar <- mu*digamma(a) - (1+mu)*digamma(b) + digamma(Phi+1)
                   
                   dldd <- ystar - mustar
                   
                   dldd
                  }, 
                 d2ldd2 = function(mu,sigma){
                   Phi <-  (1+sigma)
                   a <- mu*(1+sigma)
                   b <- mu*(1+sigma)+sigma+2 
                   
                   d2ldd2 <- -(mu^2)*trigamma(a) + ((1+mu)^2)*trigamma(b) - trigamma(Phi+1)
                   
                   d2ldd2
                   
                }, 
                 d2ldmdd = function(mu,sigma){
                   
                   a <- mu*(1+sigma)
                   b <- mu*(1+sigma)+sigma+2
                   Phi <-  (1+sigma)  
                   gammaast <- Phi*(trigamma(b) + mu*(trigamma(b)-trigamma(a)))
                   
                   d2ldmdd <- gammaast
                   
                   d2ldmdd
                
                   }, 
                 G.dev.incr = function(y, mu, sigma,...){-2*dBP(y, mu, sigma, log = TRUE)}, 
                 rqres = expression(rqres(pfun = "pBP", type = "Continuous", y = y, mu = mu, sigma = sigma)), 
                 mu.initial = expression({mu <- mean(y)}), 
                 sigma.initial = expression({sigma <-  mean(y)*(1+mean(y))/var(y) }), 
                 mu.valid = function(mu) all(mu > 0), 
                 sigma.valid = function(sigma) all(sigma > 0), 
                 y.valid = function(y) all(y > 0)),
                class = c("gamlss.family","family"))
}

